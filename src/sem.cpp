#include <cstddef>
#include <stdio.h>
#include <string.h>

extern "C" {
#include "cc.h"
//#include "malloc.h"
#include "scan.h"
#include "sem.h"
#include "semutil.h"
#include "sym.h"
}

#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <list>
#include <map>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#define MAXLOOPNEST 50
#define MAXLABELS 50
#define MAXGOTOS 50

using llvm::AllocaInst;
using llvm::ArrayType;
using llvm::BasicBlock;
using llvm::BranchInst;
using llvm::Constant;
using llvm::ConstantAggregateZero;
using llvm::ConstantInt;
using llvm::Function;
using llvm::FunctionType;
using llvm::GlobalValue;
using llvm::GlobalVariable;
using llvm::Instruction;
using llvm::IntegerType;
using llvm::IRBuilder;
using llvm::LLVMContext;
using llvm::Module;
using llvm::outs;
using llvm::PointerType;
using llvm::Type;
using llvm::Value;
using std::map;
using std::string;
using std::vector;

extern int formalnum;                        /* number of formal arguments */
extern struct id_entry *formalvars[MAXLOCS]; /* entries for parameters */
extern int localnum;                         /* number of local variables  */
extern struct id_entry *localvars[MAXLOCS];  /* entries for local variables */

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::unique_ptr<Module> TheModule;

template <typename T, typename... Args>
std::unique_ptr<T> make_unique(Args &&...args) {
  return std::unique_ptr<T>(new T(std::forward<Args>(args)...));
}

static int label_index = 0;
int relexpr = 0;

struct loopscope {
  struct sem_rec *breaks;
  struct sem_rec *conts;
} lscopes[MAXLOOPNEST];

static int looplevel = 0;
struct loopscope *looptop = (struct loopscope *)NULL;

struct labelnode {
  const char *id; /* label string    */
  BasicBlock *bb; /* basic block for label */
} labels[MAXLABELS];

struct gotonode {
  const char *id;     /* label string in goto statement */
  BranchInst *branch; /* branch to temporary label */
} gotos[MAXGOTOS];    /* list of gotos to be backpatched */

int numgotos = 0;    /* number of gotos to be backpatched */
int numlabelids = 0; /* total label ids in function */

std::string new_label() { return ("L" + std::to_string(label_index++)); }

BasicBlock *create_tmp_label() { return BasicBlock::Create(TheContext); }

BasicBlock *create_named_label(std::string label) {
  Function *curr_func = Builder.GetInsertBlock()->getParent();
  BasicBlock *new_block = BasicBlock::Create(TheContext, label, curr_func);
  return new_block;
}

/*
 * convert an internal csem type (s_type or i_type) to an LLVM Type*
 */
Type *get_llvm_type(int type) {
  switch (type & ~(T_ARRAY | T_ADDR)) {
  case T_INT:
    return Type::getInt32Ty(TheContext);
    break;
  case T_DOUBLE:
    return Type::getDoubleTy(TheContext);
    break;
  default:
    fprintf(stderr, "get_llvm_type: invalid type %x\n", type);
    exit(1);
    break;
  }
}

/*
 * startloopscope - start the scope for a loop
 */
void startloopscope() {
  looptop = &lscopes[looplevel++];
  if (looptop > lscopes + MAXLOOPNEST) {
    fprintf(stderr, "loop nest too great\n");
    exit(1);
  }
  looptop->breaks = (struct sem_rec *)NULL;
  looptop->conts = (struct sem_rec *)NULL;
}

/*
 * endloopscope - end the scope for a loop
 */
void endloopscope() {
  looplevel--;
  looptop--;
}

/*
 * Global allocations. Globals are initialized to 0.
 */
void global_alloc(struct id_entry *p, int width) {
  string name(p->i_name);
  GlobalVariable *var;
  Type *type;
  Constant *init;

  if (p->i_type & T_ARRAY) {
    type = ArrayType::get(get_llvm_type(p->i_type), width);
    init = ConstantAggregateZero::get(type);
  } else {
    type = get_llvm_type(p->i_type);
    init = ConstantInt::get(get_llvm_type(T_INT), 0);
  }

  TheModule->getOrInsertGlobal(name, type);
  var = TheModule->getNamedGlobal(name);
  var->setInitializer(init);
  p->i_value = (void *)var;
}

/*
 * backpatch - set temporary labels in the sem_rec to real labels
 *
 * LLVM API calls:
 *
 * llvm::dyn_cast<BranchInst>(Value*)
 * BranchInst::getNumSuccessors()
 * BranchInst::getSuccessor(unsigned)
 * BranchInst::setSuccessor(unsigned, BasicBlock*)
 */
void backpatch(struct sem_rec *rec, void *bb) {
  unsigned i;
  BranchInst *br_inst = nullptr;

  // for each successor of the branch, set successor for branches
  // NOTE: Does not handle certain cases at the moment (TODO)
    // May be a list of things to backpatch
  if ((br_inst = llvm::dyn_cast<BranchInst>((Value *)rec->s_value))) {
    for (i = 0; i < br_inst->getNumSuccessors(); i++) {
      if (br_inst->getSuccessor(i) == ((BasicBlock *)rec->s_bb)) {
         br_inst->setSuccessor(i, (BasicBlock *)bb);
      }
    }
  } else {
    fprintf(stderr, "error: backpatch with non-branch instruction\n");
    exit(1);
  }
  
  // backpatch the rest of the branch instructions
  if (rec->s_link) {
    backpatch(rec->s_link, bb);
  }
}

/*
 * call - procedure invocation
 *
 * Grammar:
 * lval -> ID '(' ')'            { $$ = call($1, (struct sem_rec *) NULL); }
 * lval -> ID '(' exprs ')'      { $$ = call($1, $3); }
 *
 * LLVM API calls:
 * makeArrayRef(vector<Value*>)
 * IRBuilder::CreateCall(Function *, ArrayRef<Value*>)
 */
struct sem_rec *call(char *f, struct sem_rec *args) {

  // Look up f in the symbol table
  struct id_entry *entry = lookup(f, 0);
  if (entry == NULL) {
    fprintf(stderr, "undefined function called?\n");
    return NULL;
  } 

  // Get the function
  Function *F = (Function *)entry->i_value;

  // Loop through the arguments and throw them onto a vector
  vector<Value *> vec_args;
  struct sem_rec *current_arg = args;
  while (current_arg != NULL) {
    vec_args.push_back((Value *) current_arg->s_value);
    current_arg = current_arg ->s_link;
  }

  // TODO: return s_node instead
  return s_node(Builder.CreateCall(F, makeArrayRef(vec_args)), entry->i_type);
}

/*
 * ccand - logical and
 *
 * Grammar:
 * cexpr -> cexpr AND m cexpr     { $$ = ccand($1, $3, $4); }
 *
 * LLVM API calls:
 * None
 */
struct sem_rec *ccand(struct sem_rec *e1, void *m, struct sem_rec *e2) {
  
  // first, need to handle the case where the first (e1) is true, then go to e2
  backpatch(e1->s_true, m);

  // determine if e2 is true -> then AND is true
  // Otherwise, merge the false lists, either being flase = AND being false
  return node(NULL, NULL, 0, NULL, e2->s_true, merge(e1->s_false, e2->s_false));
}

/*
 * ccexpr - convert arithmetic expression to logical expression
 *
 * Grammar:
 * cexpr -> expr                  { $$ = ccexpr($1); }
 *
 * LLVM API calls:
 *
 * IRBuilder::CreateICmpNE(Value *, Value *)
 * IRBuilder::CreateFCmpONE(Value *, Value *)
 * IRBuilder::CreateCondBr(Value *, BasicBlock *, BasicBlock *)
 */
struct sem_rec *ccexpr(struct sem_rec *e) {
  BasicBlock *tmp_true, *tmp_false;
  Value *val;

  // creating the temporary labels to jump to (true and false)
  // create a branch instruction, based on the value passed in (e)
  tmp_true = create_tmp_label();
  tmp_false = create_tmp_label();
  val = Builder.CreateCondBr((Value *)e->s_value, tmp_true, tmp_false);

  // this return is confusing but basically represents (node { s_true = true,
  // s_false = false} )
  // Creates basic blocks to jump to on true and false, since we don't know where they should resolve to 
    // yet (not done parsing if statement, which is why it's structured like this.
    // Returning a semantic record, but the semantic record just contains the true and false branch (they hold semantic records) 
    // that have branch instructions that are incomplete (no / bad labels). When you know the true labels, can use this record to go back
    // and 'patch' in these things (backpatching) 
  // RETURNING A RECORD THAT CAN BE BACKPATCHED AND HAVE LABELS FILLED IN!
  return (node((void *)NULL, (void *)NULL, 0, (struct sem_rec *)NULL,
               (node(val, tmp_true, 0, (struct sem_rec *)NULL,
                     (struct sem_rec *)NULL, (struct sem_rec *)NULL)),
               (node(val, tmp_false, 0, (struct sem_rec *)NULL,
                     (struct sem_rec *)NULL, (struct sem_rec *)NULL))));
}

/*
 * ccnot - logical not
 *
 * Grammar:
 * cexpr -> NOT cexpr             { $$ = ccnot($2); }
 *
 * LLVM API calls:
 * None
 */
struct sem_rec *ccnot(struct sem_rec *e) {

  // Basically just flip the true and false (assign false to true, assign true to false)
  return node(e->s_value, e->s_bb, e->s_type, NULL, e->s_false, e->s_true);
}

/*
 * ccor - logical or
 *
 * Grammar:
 * cexpr -> cexpr OR m cexpr      { $$ = ccor($1, $3, $4); }
 *
 * LLVM API calls:
 * None -- but uses backpatch
 */
struct sem_rec *ccor(struct sem_rec *e1, void *m, struct sem_rec *e2) {

  // backpatch
  // If e1 is false, go to e2 and evaluate
  backpatch(e1->s_false, m);

  // If e1 or e2 are true (merge), then OR is true
  // If e2 is false, then statement is false
  return node(NULL, NULL, 0, NULL, merge(e1->s_true, e2->s_true), e2->s_false);
}

/*
 * con - constant reference in an expression
 *
 * Grammar:
 * expr -> CON                   { $$ = con($1); }
 *
 * LLVM API calls:
 * ConstantInt::get(Type*, int)
 */
struct sem_rec *con(const char *x) {
  // Character string gets passed. Will insert the value into the symbol table
  // Then, uses LLVM call to create an i_value based on ConstantInt::get
  // (creates llvm constant to use) Package up content into an s_node and return
  // that
  struct id_entry *entry;

  if ((entry = lookup(x, 0)) == NULL) {
    entry = install(x, 0);
    entry->i_type = T_INT;
    entry->i_scope = GLOBAL;
    entry->i_defined = 1;
  }

  // return a sem_rec corresponding to the constant value
  entry->i_value = (void *)ConstantInt::get(get_llvm_type(T_INT), std::stoi(x));
  return (s_node((void *)entry->i_value, entry->i_type));
}

/*
 * dobreak - break statement
 *
 * Grammar:
 * stmt -> BREAK ';'                { dobreak(); }
 *
 * LLVM API calls:
 * None -- but uses n
 */
void dobreak() {
  if (looptop) {
    struct sem_rec *n_location = n();
    looptop->breaks = merge(looptop->breaks, n_location);
  }
}

/*
 * docontinue - continue statement
 *
 * Grammar:
 * stmt -> CONTINUE ';'              { docontinue(); }
 *
 * LLVM API calls:
 * None -- but uses n
 */
void docontinue() {
  if (looptop) {
    struct sem_rec *n_location = n();
    looptop->conts = merge(looptop->conts, n_location);
  }
}

/*
 * dodo - do statement
 *
 * Grammar:
 * stmt -> DO m s lblstmt WHILE '(' m cexpr ')' ';' m
 *                { dodo($2, $7, $8, $11); }
 *
 * LLVM API calls:
 * None -- but uses backpatch
 */
void dodo(void *m1, void *m2, struct sem_rec *cond, void *m3) {
  // backpatch some stuff
  backpatch(cond->s_true, m1);
  backpatch(cond->s_false, m3);

  // handle continues and breaks
  if (looptop && looptop->conts) {
    backpatch(looptop->conts, m2);
  }

  if (looptop && looptop->breaks) {
    backpatch(looptop->breaks, m3);
  }

  endloopscope();
}

/*
 * dofor - for statement
 *
 * Grammar:
 * stmt -> FOR '(' expro ';' m cexpro ';' m expro n ')' m s lblstmt n m
 *               { dofor($5, $6, $8, $10, $12, $15, $16); }
 *
 * LLVM API calls:
 * None -- but uses backpatch
 */
void dofor(void *m1, struct sem_rec *cond, void *m2, struct sem_rec *n1,
           void *m3, struct sem_rec *n2, void *m4) {
  // If condition is true, go into loop body 
  // Otherwise, if false, jump to after the loop and exit
  if (cond != NULL) {
    backpatch(cond->s_true, m3);
    backpatch(cond->s_false, m4); 
  }

  backpatch(n2, m2);
  backpatch(n1, m1);

  if (looptop && looptop->conts) {
    backpatch(looptop->conts, m2);
  }

  if (looptop && looptop->breaks){
    backpatch(looptop->breaks, m4);
  }

  endloopscope();
}

/*
 * dogoto - goto statement
 *
 * Grammar:
 * stmt -> GOTO ID ';'              { dogoto($2); }
 *
 * LLVM API calls:
 * IRBuilder::CreateBr(BasicBlock *)
 */
void dogoto(char *id) {

  if (numgotos >= MAXGOTOS) {
    fprintf(stderr, "Too many goto statements\n");
    exit(1);
  }
  
  // Go ahead and look to see if the branch exists already. If so, just branch to it & return
  for (int i = 0; i < numlabelids; i++) {
    if (strcmp(labels[i].id, id) == 0) {
      Builder.CreateBr(labels[i].bb);
      return;
    }
  }

  // If the branch DNE, then go ahead and make a temp block and branch to it. 
  BasicBlock *target = create_tmp_label(); 
  BranchInst *instr = Builder.CreateBr(target);
  
  // Set / save the id and branch for backpatching, also increment numgotos
  gotos[numgotos].id = id;
  gotos[numgotos].branch = instr;
  numgotos++;
}

/*
 * doif - one-arm if statement
 *
 * Grammar:
 * stmt -> IF '(' cexpr ')' m lblstmt m
 *         { doif($3, $5, $7); }
 *
 * LLVM API calls:
 * None -- but uses backpatch
 */
void doif(struct sem_rec *cond, void *m1, void *m2) {
  backpatch(cond->s_true, m1);
  backpatch(cond->s_false, m2);
}

/*
 * doifelse - if then else statement
 *
 * Grammar:
 * stmt -> IF '(' cexpr ')' m lblstmt ELSE n m lblstmt m
 *                { doifelse($3, $5, $8, $9, $11); }
 *
 * LLVM API calls:
 * None -- but uses backpatch
 */
void doifelse(struct sem_rec *cond, void *m1, struct sem_rec *n, void *m2,
              void *m3) {

  // if true, go to m1 (if)
  // if false, go to m2 (else)
  // backpatch n, jump to m (end of the else if)
  backpatch(cond->s_true, m1);
  backpatch(cond->s_false, m2);
  backpatch(n, m3);
}

/*
 * doret - return statement
 *
 * Grammar:
 * stmt -> RETURN ';'            { doret((struct sem_rec *) NULL); }
 * stmt -> RETURN expr ';'       { doret($2); }
 *
 * LLVM API calls:
 * IRBuilder::CreateRetVoid();
 * IRBuilder::CreateRet(Value *);
 */
void doret(struct sem_rec *e) {
  if (!e) {
    Builder.CreateRetVoid();
    return;
  }

  Builder.CreateRet( ((Value *) e->s_value) );
}

/*
 * dowhile - while statement
 *
 * Grammar:
 * stmt -> WHILE '(' m cexpr ')' m s lblstmt n m
 *                { dowhile($3, $4, $6, $9, $10); }
 *
 * LLVM API calls:
 * None -- but uses backpatch
 */
void dowhile(void *m1, struct sem_rec *cond, void *m2, struct sem_rec *n,
             void *m3) {

  // Backpatch for the condition being true -> jump to m2
  // Backpatch for the condition being false -> jump to m3 (outside of loop)
  // Backpatch for n1->m1 to check the loop condition again (iteration)
  backpatch(cond->s_true, m2);
  backpatch(cond->s_false, m3);
  backpatch(n, m1);

  // handle the breaks and continues
  if (looptop && looptop->conts) {
    // check the continues -> go to the loop condition 
    backpatch(looptop->conts, m1);
  }

  // check breaks -> go to loop exit
  if (looptop && looptop->breaks) {
    backpatch(looptop->breaks, m3);
  }

  // end the scope for the loop
  endloopscope();
}

/*
 * exprs - form a list of expressions
 *
 * Grammar:
 * exprs -> exprs ',' expr        { $$ = exprs($1, $3); }
 *
 * LLVM API calls:
 * None
 */
struct sem_rec *exprs(struct sem_rec *l, struct sem_rec *e) {
  // NOTE: Will return a single expression
  if (l == NULL) return e;

  struct sem_rec *current_entry = l;

  // Loop through the list of expressions until the end. 
  // Then, insert the new entry onto this list
  while (current_entry->s_link != NULL) {
    current_entry = current_entry->s_link;
  }

  current_entry->s_link = e;
  return l;
}

/*
 * fhead - beginning of function body
 *
 * Grammar:
 * fhead -> fname fargs '{' dcls  { fhead($1); }
 */
void fhead(struct id_entry *p) {
  Type *func_type, *var_type;
  Value *arr_size;
  vector<Type *> func_args;
  GlobalValue::LinkageTypes linkage;
  FunctionType *FT;
  Function *F;
  BasicBlock *B;
  int i;
  struct id_entry *v;

  /* get function return type */
  func_type = get_llvm_type(p->i_type);

  /* get function argument types */
  for (i = 0; i < formalnum; i++) {
    func_args.push_back(get_llvm_type(formalvars[i]->i_type));
  }

  FT = FunctionType::get(func_type, makeArrayRef(func_args), false);

  /* linkage is external if function is main */
  linkage = (strcmp(p->i_name, "main") == 0) ? Function::ExternalLinkage
                                             : Function::InternalLinkage;

  F = Function::Create(FT, linkage, p->i_name, TheModule.get());
  p->i_value = (void *)F;

  B = BasicBlock::Create(TheContext, "", F);
  Builder.SetInsertPoint(B);

  /*
   * Allocate instances of each parameter and local so they can be referenced
   * and mutated.
   */
  i = 0;
  for (auto &arg : F->args()) {

    v = formalvars[i++];
    arg.setName(v->i_name);
    var_type = get_llvm_type(v->i_type);
    arr_size = (v->i_width > 1)
                   ? (ConstantInt::get(get_llvm_type(T_INT), v->i_width))
                   : NULL;

    v->i_value = Builder.CreateAlloca(var_type, arr_size, arg.getName());
    Builder.CreateStore(&arg, (Value *)v->i_value);
  }

  /* Create the instance of stack memory for each local variable */
  for (i = 0; i < localnum; i++) {
    v = localvars[i];
    var_type = get_llvm_type(v->i_type);
    arr_size = (v->i_width > 1)
                   ? (ConstantInt::get(get_llvm_type(T_INT), v->i_width))
                   : NULL;

    v->i_value =
        Builder.CreateAlloca(var_type, arr_size, std::string(v->i_name));
  }
}

/*
 * fname - function declaration
 *
 * Grammar:
 * fname -> type ID               { $$ = fname($1, $2); }
 * fname -> ID                    { $$ = fname(T_INT, $1); }
 */
struct id_entry *fname(int t, char *id) {
  struct id_entry *entry = lookup(id, 0);

  // add function to hash table if it doesn't exist
  if (!entry) {
    entry = install(id, 0);
  }

  // cannot have two functions of the same name
  if (entry->i_defined) {
    yyerror("cannot declare function more than once");
  }

  entry->i_type = t;
  entry->i_scope = GLOBAL;
  entry->i_defined = true;

  // need to enter the block to let hash table do internal work
  enterblock();
  // then need to reset argument count variables

  formalnum = 0;
  localnum = 0;

  return entry;
}

/*
 * ftail - end of function body
 *
 * Grammar:
 * func -> fhead stmts '}'       { ftail(); }
 */
void ftail() {
  numgotos = 0;
  numlabelids = 0;
  leaveblock();
}

/*
 * id - variable reference
 *
 * Grammar:
 * lval -> ID                    { $$ = id($1); }
 * lval -> ID '[' expr ']'       { $$ = indx(id($1), $3); }
 *
 * LLVM API calls:
 * None
 */
struct sem_rec *id(char *x) {
  struct id_entry *entry;

  if ((entry = lookup(x, 0)) == NULL) {
    yyerror("undeclared identifier");
    entry = install(x, -1);
    entry->i_type = T_INT;
    entry->i_scope = LOCAL;
    entry->i_defined = 1;
  }

  // insert identifier into the symbol table
  // Return a  semantic record with a value corresponding to that identifier
  // Constructor that takes an LLVM value and a type
  // It will call the node constructor which will then fill in and save a
  // semantic record
  return (s_node((void *)entry->i_value, entry->i_type | T_ADDR));
}

/*
 * indx - subscript
 *
 * Grammar:
 * lval -> ID '[' expr ']'       { $$ = indx(id($1), $3); }
 *
 * LLVM API calls:
 * makeArrayRef(vector<Value*>)
 * IRBuilder::CreateGEP(Type, Value *, ArrayRef<Value*>)
 */
struct sem_rec *indx(struct sem_rec *x, struct sem_rec *i) {


  vector<Value*> indices;  
  indices.push_back((Value *)i->s_value);

  Value *instr = Builder.CreateGEP(get_llvm_type(x->s_type), (Value *)x->s_value, makeArrayRef(indices));

  return s_node(instr, (x->s_type & ~T_ARRAY));  
}

/*
 * labeldcl - process a label declaration
 *
 * Grammar:
 * labels -> ID ':'                { labeldcl($1); }
 * labels -> labels ID ':'         { labeldcl($2); }
 *
 * NOTE: All blocks in LLVM must have a terminating instruction (i.e., branch
 * or return statement -- fall-throughs are not allowed). This code must
 * ensure that each block ends with a terminating instruction.
 *
 * LLVM API calls:
 * IRBuilder::GetInsertBlock()
 * BasicBlock::getTerminator()
 * IRBuilder::CreateBr(BasicBlock*)
 * IRBuilder::SetInsertPoint(BasicBlock*)
 * BranchInst::setSuccessor(unsigned, BasicBlock*)
 */
void labeldcl(const char *id) {

  // Check if there are too many labels
  if (numlabelids >= MAXLABELS) {
    fprintf(stderr, "Too many labels\n");
    exit(1);
  }
  
  // Create block with specific name to match output
  BasicBlock *bb = create_named_label(std::string("userlbl_") + id);

  // now, check the current block for any termination.
  // If it doesn't have one, then create a branch
  if (Builder.GetInsertBlock()->getTerminator() == NULL) {
    Builder.CreateBr(bb);
  }

  // store the label info
  labels[numlabelids].id = id;
  labels[numlabelids].bb = bb;
  numlabelids++;

  Builder.SetInsertPoint(bb);

  // backpatch any of the current existing gotos here
  for (int i =0; i < numgotos; i++) {
    if (gotos[i].id && strcmp(gotos[i].id, id) == 0) {
      gotos[i].branch->setSuccessor(0, bb);
      gotos[i].id = NULL;
    }
  }
}

/*
 * m - generate label and return next temporary number
 *
 * NOTE: All blocks in LLVM must have a terminating instruction (i.e., branch
 * or return statement -- fall-throughs are not allowed). This code must
 * ensure that each block ends with a terminating instruction.
 *
 * LLVM API calls:
 * IRBuilder::GetInsertBlock()
 * BasicBlock::getTerminator()
 * IRBuilder::CreateBr(BasicBlock*)
 * IRBuilder::SetInsertPoint(BasicBlock*)
 */
void *m() {
  BasicBlock *bb;

  std::string label = new_label();
  bb = create_named_label(label);

  // In LLVM, every block has to end with a branch instr or retunr
  // if end of block you are in is NOT a branch instr or return ,you insert one
  if (Builder.GetInsertBlock()->getTerminator() == NULL) {
    Builder.CreateBr(bb);
  }

  // Then, set the insert point to this BB
  // Any new instructions generated with API will be at this block
  // For example, now in the first m block of the code example given: if ( cexpr ) m lblstmt m
  Builder.SetInsertPoint(bb);
  return (void *) bb;
}

/*
 * n - generate goto and return backpatch pointer
 *
 * LLVM API calls:
 * IRBuilder::CreateBr(BasicBlock *)
 */
struct sem_rec *n() {
  // create target for the goto
  // create unconditional branch instr
  // create and return record for backpatching
  BasicBlock *targetBlock = create_tmp_label();
  Value *branch = Builder.CreateBr(targetBlock);

  return node(branch, targetBlock, 0, NULL, NULL, NULL);
}

/*
 * op1 - unary operators
 *
 * LLVM API calls:
 * IRBuilder::CreateLoad(Type, Value *)
 * IRBuilder::CreateNot(Value *)
 * IRBuilder::CreateNeg(Value *)
 * IRBuilder::CreateFNeg(Value *)
 */
struct sem_rec *op1(const char *op, struct sem_rec *y) {

  struct sem_rec *rec = nullptr;

  // for line 217 in cgram.y, handles the op1 ('@', id) call
  if (*op == '@') {
    if (!(y->s_type & T_ARRAY)) {
      y->s_type &= ~T_ADDR;
      // Creates a load instr in the ll code
      rec = s_node(
          Builder.CreateLoad(get_llvm_type(y->s_type), ((Value *)y->s_value)),
          y->s_type);
    }
  }

  // TODO: Remainder of this function, handle "~", "-"
  else if (*op == '-') {
    fprintf(stderr, "op1: handling the '-' operator is not implemented\n");
    return NULL;
  } else if (*op == '~') {
    // TODO: INTEGERS ONLY!
    fprintf(stderr, "op1: handling the '~' operator is not implemented\n");
    return NULL;
  }

  return rec;
}

/*
 * op2 - arithmetic operators
 *
 * No LLVM API calls, but most functionality is abstracted to a separate
 * method used by op2, opb, and set.
 *
 * The separate method uses the following API calls:
 * IRBuilder::CreateAdd(Value *, Value *)
 * IRBuilder::CreateFAdd(Value *, Value *)
 * IRBuilder::CreateSub(Value *, Value *)
 * IRBuilder::CreateFSub(Value *, Value *)
 * IRBuilder::CreateMul(Value *, Value *)
 * IRBuilder::CreateFMul(Value *, Value *)
 * IRBuilder::CreateSDiv(Value *, Value *)
 * IRBuilder::CreateFDiv(Value *, Value *)
 * IRBuilder::CreateSRem(Value *, Value *)
 * IRBuilder::CreateAnd(Value *, Value *)
 * IRBuilder::CreateOr(Value *, Value *)
 * IRBuilder::CreateXOr(Value *, Value *)
 * IRBuilder::CreateShl(Value *, Value *)
 * IRBuilder::CreateAShr(Value *, Value *)
 */
struct sem_rec *op2(const char *op, struct sem_rec *x, struct sem_rec *y) {

  // cast if needed
  if (x->s_type != y->s_type) {
    y = cast(y, x->s_type);
  } 

  struct sem_rec *val = nullptr;

  if (strcmp(op, "+") == 0) {
    if (x->s_type & T_INT) {
      val = s_node(Builder.CreateAdd((Value *) x->s_value, (Value *) y->s_value), x->s_type);
    }
    else if (x->s_type & T_DOUBLE) {
      val = s_node(Builder.CreateFAdd((Value *) x->s_value, (Value *) y->s_value), x->s_type);
    } 
  } else if (strcmp(op, "-") == 0) {
    if (x->s_type & T_INT) {
      val = s_node(Builder.CreateSub((Value *) x->s_value, (Value *) y->s_value), x->s_type);
    }
    else if (x->s_type & T_DOUBLE) {
      val = s_node(Builder.CreateFSub((Value *) x->s_value, (Value *) y->s_value), x->s_type);
    }
  } else if (strcmp(op, "*") == 0) {
    if (x->s_type & T_INT) {
      val = s_node(Builder.CreateMul((Value *) x->s_value, (Value *) y->s_value), x->s_type);
    }
    else if (x->s_type & T_DOUBLE) {
      val = s_node(Builder.CreateFMul((Value *) x->s_value, (Value *) y->s_value), x->s_type);
    }
  } else if (strcmp(op, "/") == 0) {
    if (x->s_type & T_INT) {
      val = s_node(Builder.CreateSDiv((Value *) x->s_value, (Value *) y->s_value), x->s_type);
    }
    else if (x->s_type & T_DOUBLE) {
      val = s_node(Builder.CreateFDiv((Value *) x->s_value, (Value *) y->s_value), x->s_type);
    }
  } else if (strcmp(op, "%") == 0) {
    if (x->s_type & T_INT) {
      val = s_node(Builder.CreateSRem((Value *) x->s_value, (Value *) y->s_value), x->s_type);
    } else {
      fprintf(stderr, "op2 error: Calling mod with doubles not allowed\n");
      return NULL;
    }
  } 

  return val;
}

/*
 * opb - bitwise operators
 *
 * No LLVM API calls, but most functionality is abstracted to a separate
 * method used by op2, opb, and set. The comment above op2 lists the LLVM API
 * calls for this method.
 */
struct sem_rec *opb(const char *op, struct sem_rec *x, struct sem_rec *y) {

  struct sem_rec *val = nullptr;

  if (strcmp(op, "|") == 0) {
    if (x->s_type & T_INT) {
      val = s_node(Builder.CreateOr((Value *) x->s_value, (Value *) y->s_value), x->s_type);
    }
  } else if (strcmp(op, "^") == 0) {
    if (x->s_type & T_INT) {
      val = s_node(Builder.CreateXor((Value *) x->s_value, (Value *) y->s_value), x->s_type);
    }
  } else if (strcmp(op, "&") == 0) {
    if (x->s_type & T_INT) {
      val = s_node(Builder.CreateAnd((Value *) x->s_value, (Value *) y->s_value), x->s_type);
    }
  } else if (strcmp(op, "<<") == 0) {
    if (x->s_type & T_INT) {
      val = s_node(Builder.CreateShl((Value *) x->s_value, (Value *) y->s_value), x->s_type);
    }
  } else if (strcmp(op, ">>") == 0) {
    if (x->s_type & T_INT) {
      val = s_node(Builder.CreateAShr((Value *) x->s_value, (Value *) y->s_value), x->s_type);
    }
  }
  
  return val;
}

/*
 * rel - relational operators
 *
 * Grammar:
 * cexpr -> expr EQ expr          { $$ = rel((char*) "==", $1, $3); }
 * cexpr -> expr NE expr          { $$ = rel((char*) "!=", $1, $3); }
 * cexpr -> expr LE expr          { $$ = rel((char*) "<=", $1, $3); }
 * cexpr -> expr GE expr          { $$ = rel((char*) ">=", $1, $3); }
 * cexpr -> expr LT expr          { $$ = rel((char*) "<",  $1, $3); }
 * cexpr -> expr GT expr          { $$ = rel((char*) ">",  $1, $3); }
 *
 * LLVM API calls:
 * IRBuilder::CreateICmpEq(Value *, Value *)
 * IRBuilder::CreateFCmpOEq(Value *, Value *)
 * IRBuilder::CreateICmpNE(Value *, Value *)
 * IRBuilder::CreateFCmpONE(Value *, Value *)
 * IRBuilder::CreateICmpSLT(Value *, Value *)
 * IRBuilder::CreateFCmpOLT(Value *, Value *)
 * IRBuilder::CreateICmpSLE(Value *, Value *)
 * IRBuilder::CreateFCmpOLE(Value *, Value *)
 * IRBuilder::CreateICmpSGT(Value *, Value *)
 * IRBuilder::CreateFCmpOGT(Value *, Value *)
 * IRBuilder::CreateICmpSGE(Value *, Value *)
 * IRBuilder::CreateFCmpOGE(Value *, Value *)
 */
struct sem_rec *rel(const char *op, struct sem_rec *x, struct sem_rec *y) {

  Value *val = nullptr;

  // INT LESS THAN
  if (*op == '<') {
    if (x->s_type & T_INT && y->s_type & T_INT) {
      val = Builder.CreateICmpSLT((Value *)x->s_value, (Value *)y->s_value);
    }
    else if (x->s_type & T_DOUBLE || y->s_type & T_DOUBLE) {
      if (!(x->s_type & T_DOUBLE)) {
        x = cast(x, T_DOUBLE);
      }
      else if (!(y->s_type & T_DOUBLE)){
        y = cast(y, T_DOUBLE);
      }

      val = Builder.CreateFCmpOLT((Value *)x->s_value, (Value *)y->s_value);
    }
  }

  // GREATER THAN
  else if (*op == '>') {
    if (x->s_type & T_INT && y->s_type & T_INT) {
      val = Builder.CreateICmpSGT((Value *)x->s_value, (Value *)y->s_value);
    }
    else if (x->s_type & T_DOUBLE || y->s_type & T_DOUBLE) {
      if (!(x->s_type & T_DOUBLE)) {
        x = cast(x, T_DOUBLE);
      }
      else if (!(y->s_type & T_DOUBLE)) {
        y = cast(y, T_DOUBLE);
      }

      val = Builder.CreateFCmpOGT((Value *)x->s_value, (Value *)y->s_value);
    }
  }

  // EQUALS
  else if (strcmp(op, "==") == 0) {
    if (x->s_type & T_INT && y->s_type & T_INT) {
      val = Builder.CreateICmpEQ((Value *)x->s_value, (Value *)y->s_value);
    }
    else if (x->s_type & T_DOUBLE || y->s_type & T_DOUBLE) {
      if (!(x->s_type & T_DOUBLE)) {
        x = cast(x, T_DOUBLE);
      }
      else if (!(y->s_type & T_DOUBLE)){
        y = cast(y, T_DOUBLE);
      }

      val = Builder.CreateFCmpOEQ((Value *)x->s_value, (Value *)y->s_value);
    } 
  }

  // NOT EQUAL
  else if (strcmp(op, "!=") == 0) {
    if (x->s_type & T_INT && y->s_type & T_INT) {
      val = Builder.CreateICmpNE((Value *)x->s_value, (Value *)y->s_value);
    }
    else if (x->s_type & T_DOUBLE || y->s_type & T_DOUBLE) {
      if (!(x->s_type & T_DOUBLE)) {
        x = cast(x, T_DOUBLE);
      }
      else if (!(y->s_type & T_DOUBLE)){
        y = cast(y, T_DOUBLE);
      }

      val = Builder.CreateFCmpONE((Value *)x->s_value, (Value *)y->s_value);
    }
  }

  // LESS THAN EQUAL TO
  else if (strcmp(op, "<=") == 0) {
    if (x->s_type & T_INT && y->s_type & T_INT) {
      val = Builder.CreateICmpSLE((Value *)x->s_value, (Value *)y->s_value);
    }
    else if (x->s_type & T_DOUBLE || y->s_type & T_DOUBLE) {
      if (!(x->s_type & T_DOUBLE)) {
        x = cast(x, T_DOUBLE);
      }
      else if (!(y->s_type & T_DOUBLE)){
        y = cast(y, T_DOUBLE);
      }

      val = Builder.CreateFCmpOLE((Value *)x->s_value, (Value *)y->s_value);
    }

  }
  // GREATER THAN EQUAL TO
  // * IRBuilder::CreateICmpSGE(Value *, Value *)
 // * IRBuilder::CreateFCmpOGE(Value *, Value *)
  else if (strcmp(op, ">=") == 0) {
    if (x->s_type & T_INT && y->s_type & T_INT) {
      val = Builder.CreateICmpSGE((Value *)x->s_value, (Value *)y->s_value);
    }
    // Check and if one of them is a double, cast the other to a double
    else if (x->s_type & T_DOUBLE || y->s_type & T_DOUBLE) {
      if (!(x->s_type & T_DOUBLE)) {
        x = cast(x, T_DOUBLE);
      }
      else if (!(y->s_type & T_DOUBLE)){
        y = cast(y, T_DOUBLE);
      }

      val = Builder.CreateFCmpOGE((Value *)x->s_value, (Value *)y->s_value);
    }
  }
  
  return (ccexpr(s_node((void *)val, T_INT)));
}

/*
 * cast - cast value to a different type
 *
 * LLVM API calls:
 * IRBuilder::CreateSIToFP(Value *, Type *)
 * IRBuilder::CreateFPToSI(Value *, Type *)
 */
struct sem_rec *cast(struct sem_rec *y, int t) {
  
  Value *val = (Value *)y->s_value;
  
  // Convert y type & value depending on t
  if (t & T_DOUBLE) {
    val = Builder.CreateSIToFP(val, get_llvm_type(t));
    y->s_type = t;
    y->s_value = val;
  } 
  else if (t & T_INT) {
    val = Builder.CreateFPToSI(val, get_llvm_type(t));
    y->s_type = t;
    y->s_value = val;
  }
    return y;
}

/*
 * set - assignment operators
 *
 * Grammar:
 * expr -> lval SET expr         { $$ = set((char*) "",   $1, $3); }
 * expr -> lval SETOR expr       { $$ = set((char*) "|",  $1, $3); }
 * expr -> lval SETXOR expr      { $$ = set((char*) "^",  $1, $3); }
 * expr -> lval SETAND expr      { $$ = set((char*) "&",  $1, $3); }
 * expr -> lval SETLSH expr      { $$ = set((char*) "<<", $1, $3); }
 * expr -> lval SETRSH expr      { $$ = set((char*) ">>", $1, $3); }
 * expr -> lval SETADD expr      { $$ = set((char*) "+",  $1, $3); }
 * expr -> lval SETSUB expr      { $$ = set((char*) "-",  $1, $3); }
 * expr -> lval SETMUL expr      { $$ = set((char*) "*",  $1, $3); }
 * expr -> lval SETDIV expr      { $$ = set((char*) "/",  $1, $3); }
 * expr -> lval SETMOD expr      { $$ = set((char*) "%",  $1, $3); }
 *
 * Much of the functionality in this method is abstracted to a separate method
 * used by op2, opb, and set. The comment above op2 lists the LLVM API calls
 * for this method.
 *
 * Additional LLVM API calls:
 * IRBuilder::CreateLoad(Type, Value *)
 * IRBuilder::CreateStore(Value *, Value *)
 */
struct sem_rec *set(const char *op, struct sem_rec *x, struct sem_rec *y) {
  if (x->s_type != y->s_type) {
    y = cast(y, x->s_type);
  }

  // NOTE: THIS IS FOR ""
  if (strcmp(op, "") == 0) {
    Builder.CreateStore((Value *) y->s_value, (Value *) x->s_value);
    return x; 
  }

  // load
  Value *loaded_x = Builder.CreateLoad(get_llvm_type(x->s_type), (Value*)x->s_value);

  // op2 / opb
  struct sem_rec *x_new = s_node(loaded_x, x->s_type);
  struct sem_rec *result = nullptr;


  if (strcmp(op, "+") == 0 || strcmp(op, "-") == 0 || strcmp(op, "*") == 0 || strcmp(op, "/") == 0 || strcmp(op, "%") == 0) {
    result = op2(op, x_new, y); 
  } else {
    result = opb(op, x_new, y);
  }

  // store
  if (result != NULL) Builder.CreateStore((Value *)result->s_value, (Value*) x->s_value);

  return result;
}

/*
 * genstring - generate code for a string
 *
 * Grammar:
 * expr ->  STR                   { $$ = genstring($1); }
 *
 * Use parse_escape_chars (in semutil.c) to handle escape characters
 *
 * LLVM API calls:
 * IRBuilder::CreateGlobalStringPtr(char *)
 */
struct sem_rec *genstring(char *s) {

  // Will call parse_escape_chars on s i guess
  // Then, create global string ptr 
  char *new_str = parse_escape_chars(s);
  struct sem_rec *rec;

  return s_node(Builder.CreateGlobalStringPtr(new_str), T_STR); 
}

void declare_print() {
  struct id_entry *entry;
  FunctionType *var_arg;
  Value *F;
  std::string fname = "print";

  /* Add print to our internal data structure */
  var_arg =
      FunctionType::get(IntegerType::getInt32Ty(TheContext),
                        PointerType::get(Type::getInt8Ty(TheContext), 0), true);
  F = TheModule->getOrInsertFunction(fname, var_arg).getCallee();

  entry = install(slookup(fname.c_str()), 0);
  entry->i_type = T_INT | T_PROC;
  entry->i_value = (void *)F;
}

void init_IR() {
  TheModule = make_unique<Module>("<stdin>", TheContext);
  declare_print();
}

void emit_IR() { TheModule->print(outs(), nullptr); }
