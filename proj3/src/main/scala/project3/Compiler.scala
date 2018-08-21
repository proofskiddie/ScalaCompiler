package project3

abstract class X86Compiler extends BugReporter with Codegen {
  import Language._

  /*
   * Abstract class used to store the location
   */
  abstract class Loc {
    def +(y: Int): Loc
  }

  /*
   * Register location, the physical location
   * can be addressed with the register #sp
   */
  case class Reg(sp: Int) extends Loc {
    def +(y: Int) = Reg(sp+y)
  }

  /*
   * Function location, the physical location
   * can be addressed directly with the name
   */
  case class Func(name: String) extends Loc {
    def +(y: Int) = BUG("This Loc should not be used as a stack location.")
  }

  // Function to extra physical address from Loc
  // CHANGE: instead of using regs(...) directly
  // we know use the function loc.
  def loc(l: Loc): String = l match {
    case Reg(sp) => avRegs(sp)
    case Func(name) => name
  }

  def loc(sp: Int): String = avRegs(sp)

  // List of available register.
  // DO NOT CHANGE THE REGISTERS!!
  val avRegs = Seq("%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15")

  /****************************************************************************/

  def onMac = System.getProperty("os.name").toLowerCase contains "mac"
  val entry_point = "entry_point"
  def funcName(name: String) = (if (onMac) "_" else "") + name

  /**
   * Env of the compiler. Keep track of the location
   * in memory of each variable defined.
   */
  val primitives = Map(
    "putchar" -> Func("putchar"),
    "getchar" -> Func("getchar"))

  private class Env {
    def undef(name: String) = BUG(s"Undefined identifier $name (should have been found during the semantic analysis)")
    def apply(name: String): Loc =  undef(name)
  }

  private case class LocationEnv(
    vars: Map[String, Loc] = primitives,
    outer: Env = new Env) extends Env {

      /*
       * Return a copy of the current state plus a
       * variable 'name' at the location 'loc'
       */
      def withVal(name: String, loc: Loc): LocationEnv = {
        copy(vars = vars + (name -> loc))
      }

      /*
       * Return a copy of the current state plus all
       * variables in 'list'
       */
      def withVals(list: List[(String,Loc)]): LocationEnv = {
        copy(vars = vars ++ list.toMap)
      }

      /*
       * Return the location of the variable 'name'
       */
      override def apply(name: String): Loc = vars.get(name) match {
        case Some(loc) => loc
        case _  => outer(name)
      }
  }

  /*
   * Generate code that computes the unary operator
   * 'op' on the value at memory location 'sp' and that
   * stores the result at 'sp'.
   */
  def transUn(op: String)(sp: Loc) = op match {
    case "+" => () // nothing to do!
    case "-" => emitln(s"negq ${loc(sp)}")
    case _ => BUG(s"Unary operator $op undefined")
  }

  /*
   * Generate code that computes the binary operator
   * 'op' on the values at memory location 'sp' and
   * 'sp1' and that stores the result at 'sp'.
   *
   * TODO: implement missing operators.
   * Here are the valid operators:
   * +, -, *, /, ==, !=, <=, <, >=, >, block-get
   */
  def transBin(op: String)(sp: Loc, sp1: Loc) = op match {
    case "+" => emitln(s"addq ${loc(sp1)}, ${loc(sp)}")
    case "-" => emitln(s"subq ${loc(sp1)}, ${loc(sp)}")
    case "*" => emitln(s"imul ${loc(sp1)}, ${loc(sp)}")
    case "/" =>
      emitln(s"movq ${loc(sp)}, %rax")
      emitln(s"pushq %rdx") // save $rdx for the division
      emitln(s"movq ${loc(sp1)}, %rbx") // in case sp1 == %rdx
      emitln(s"cqto")
      emitln(s"idiv %rbx")
      emitln(s"popq %rdx") // put back
      emitln(s"movq %rax, ${loc(sp)}")
    case "==" =>
      emitln(s"cmp ${loc(sp + 1)}, ${loc(sp)}")
      emitln(s"sete %al")
      emitln(s"movzbq %al, ${loc(sp)}")
    case "!=" =>
      emitln(s"cmp ${loc(sp + 1)}, ${loc(sp)}")
      emitln(s"setne %al")
      emitln(s"movzbq %al, ${loc(sp)}")
    case "<=" => 
      emitln(s"cmp ${loc(sp + 1)}, ${loc(sp)}")
      emitln(s"setle %al")
      emitln(s"movzbq %al, ${loc(sp)}")
    case "<" => 
      emitln(s"cmp ${loc(sp + 1)}, ${loc(sp)}")
      emitln(s"setl %al")
      emitln(s"movzbq %al, ${loc(sp)}")
    case ">=" =>
      emitln(s"cmp ${loc(sp + 1)}, ${loc(sp)}")
      emitln(s"setge %al")
      emitln(s"movzbq %al, ${loc(sp)}")
    case ">" =>       
      emitln(s"cmp ${loc(sp + 1)}, ${loc(sp)}")
      emitln(s"setg %al")
      emitln(s"movzbq %al, ${loc(sp)}")
    case _ => BUG(s"Binary operator $op undefined")
  }

  /*
   * Generate code that computes the ternary operator
   * 'op' on the values at memory location 'sp', 'sp1 and'
   * 'sp2' and that stores the result at 'sp'.
   *
   * TODO: implement the missing operator
   * Valid operators: block-set
   */
  def transTer(op: String)(sp: Loc, sp1: Loc, sp2: Loc) = op match {
    case _ => BUG(s"ternary operator $op undefined")
  }

  def transPrim(op: String)(idxs: List[Loc]) = idxs match {
    case List(sp, sp1, sp2) => transTer(op)(sp, sp1, sp2)
    case List(sp, sp1)      => transBin(op)(sp, sp1)
    case List(sp)           => transUn(op)(sp)
    case _ => BUG(s"no prim with ${idxs.length} arguments")
  }

  type Label = String

  var nLabel = 0
  def freshLabel(pref: String) = { nLabel += 1; s"$pref$nLabel" }

  /*
   * Generate code that compute the result of the
   * computation represented by the AST 'exp'.
   */
  val global = (primitives.keySet + entry_point) map(funcName(_))
  def emitCode(exp: Exp): Unit = {
    emitln(".text", 0)
    emitln(s".global ${global mkString ", "}\n", 0)

    // Generate code for our AST
    trans(exp, Reg(0))(LocationEnv())

    emitln("#################### DATA #######################", 0)
    emitln("\n.data\nheap:\t.quad 0",0)
    emitln("#################################################", 0)
  }

  /*
   * Generate code that jump to the label 'label'
   * if the location 'sp' contains the value 'true'
   */
  def transJumpIfTrue(sp: Loc)(label: Label) = {
      emitln(s"test ${loc(sp)}, ${loc(sp)}")
      emitln(s"jne ${label}")
  }

  /*
   * Generate code that compute the result og the
   * computation represented by the AST 'exp'. The
   * value will be placed at memory location 'sp'
   *
   * TODO: Fill in each TODO with the appropriate code.
   *
   * The ??? can be filled for extra credit.
   */
  def trans(exp: Exp, sp: Loc)(env: LocationEnv): Unit = exp match {
    case Lit(x: Int) =>
      emitln(s"movq $$$x, ${loc(sp)}")
    case Lit(b: Boolean) =>
      val cstr = if (b) "$$1" else "$$0"
      emitln(s"movq ${cstr}, ${loc(sp)}")
    case Lit(x: Unit) => ()
    case Prim(op, args) =>
      val idxs = List.tabulate(args.length)(i => sp + i)
      (args zip idxs) foreach { case (arg, idx) => trans(arg, idx)(env) }
      transPrim(op)(idxs)
    case Let(x, tp, rhs, body) =>
      trans(rhs, sp)(env)
      if (tp == UnitType) { // simple optimization for Daniel
        trans(body, sp)(env)
      } else {
        trans(body, sp + 1)(env.withVal(x, sp))
        emitln(s"movq ${loc(sp + 1)}, ${loc(sp)}")
      }
    case Ref(x) =>
      env(x) match {
        case Reg(sp1) => emitln(s"movq ${loc(sp1)}, ${loc(sp)}")
        case Func(name) => name
      }
    case If(cond, tBranch, eBranch) =>
      val lab = freshLabel("if")
      trans(cond, sp)(env)
      transJumpIfTrue(sp)(s"${lab}_then")
      trans(eBranch, sp)(env)
      emitln(s"jmp ${lab}_end")
      emitln(s"${lab}_then:", 0)
      trans(tBranch, sp)(env)
      emitln(s"${lab}_end:", 0)
    case VarDec(x, tp, rhs, body) =>
      trans(rhs, sp)(env)
      trans(body, sp + 1)(env.withVal(x, sp))
      emitln(s"movq ${loc(sp + 1)}, ${loc(sp)}")
    case VarAssign(x, rhs) =>
      trans(rhs, sp)(env)
      emitln(s"movq ${loc(sp)}, ${loc(env(x))}")
    case While(cond, lBody, body) =>
      val lab = freshLabel("loop")
      emitln(s"jmp ${lab}_cond")
      emitln(s"${lab}_body:", 0)
      trans(lBody, sp)(env)
      emitln(s"${lab}_cond:", 0)
      trans(cond, sp)(env)
      transJumpIfTrue(sp)(s"${lab}_body")
      trans(body, sp)(env)
    case LetRec(funs, body) =>
      emitln("################# FUNCTIONS #####################", 0)
      // We do not save the location of the function into register because we can use their
      // name as a label.
      val funsLoc = funs map { case FunDef(name, _, _, _) => (name, Func(name)) }
      val funEnv = env.withVals(funsLoc)
      
      funs foreach { f => trans(f,Reg(0))(funEnv) }
      

      emitln("#################################################\n\n", 0)
      emitln("###################### MAIN #####################", 0)
      //////////// DO NOT CHANGE////////////////
      emitln(s"${funcName(entry_point)}:", 0)
      emitln("pushq %rbp\t# save stack frame for calling convention")
      emitln("movq %rsp, %rbp")
      emitln("movq %rdi, heap(%rip)")
      //////////////////////////////////////////

      // emit the main function (body of LetRec) here
      // TODO you may need to change that code.
      trans(body, Reg(0))(funEnv)
      emitln(s"movq ${loc(0)}, %rax")
      //////////// DO NOT CHANGE////////////////
      emitln("movq %rbp, %rsp\t# reset frame")
      emitln("popq %rbp")
      emitln("ret")
      emitln("#################################################\n\n", 0)
      //////////////////////////////////////////

    case FunDef(fname, args, _, fbody) =>
      //////////// DO NOT CHANGE////////////////
      emitln(s"${funcName(fname)}:", 0)
      emitln("pushq %rbp\t# save stack frame for calling convention")
      emitln("movq %rsp, %rbp")
      //////////////////////////////////////////
      val idxs = List.tabulate(args.length)(i => i % avRegs.length)
      val nargs = (args zip idxs) map { case (Arg(name,_,_), i) => (name,Reg(i)) }
      val argEnv = env.withVals(nargs)
      trans(fbody, Reg(0))(argEnv)
      emitln(s"movq ${loc(0)}, %rax")
      //////////// DO NOT CHANGE////////////////
      emitln("movq %rbp, %rsp\t# reset frame")
      emitln("popq %rbp")
      emitln("ret\n")
      //////////////////////////////////////////
    case App(fun, args) =>
      // Advices: you may want to start to work on function with only one argument
      // i.e. change args to List(arg). Once it is working you can generalize your
      // code and work on multiple arguments.
      // Evaluate the arguments
      val idxs = List.tabulate(args.length)(i => i % avRegs.length)
      var i = 0
      while(Reg(i) != sp) {
        emitln(s"push ${loc(i)}")
        i = i + 1
      }
      (args zip idxs) map { case (exp, i) =>
        trans(exp, Reg(i))(env) }
      // Compute the physical location of the function to be called
      val fLoc: String = fun match {
        case Ref(fname) =>
          env(fname) match {
            case Reg(sp) => ??? // Extra credit
            case Func(name) => name
          }
        case _ => ??? // Extra credit
      }
      emitln(s"call ${fLoc}")

      i = 0
      while(Reg(i) != sp) {
        emitln(s"pop ${loc(i)}")
        i = i + 1
      }

    case ArrayDec(size, _) =>
      // This node needs to allocate an area of eval(size) * 8 bytes in the heap
      // the assembly variable "heap" contains a pointer to the first valid byte
      // in the heap. Make sure to update its value accordingly.
      // TODO
      trans(size, sp)(env)
      emitln(s"movq $$8 ${loc(sp + 1)}")
      emitln(s"imulq ${loc(sp+1)} ${loc(sp)}")
      emitln(s"movq heap(%rip), %rax")
      emitln(s"movq heap(${loc(sp)}) %rip")
    case _ => BUG(s"don't know how to implement $exp")
  }
}
