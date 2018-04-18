//
// Scala implementation of bidirectional type checking & inference as described in:
// "Complete and Easy Bidirectional Type Checking for Higher-Rank Polymorphism"
// http://research.cs.queensu.ca/~joshuad/papers/bidir/

package bidir

object Bidir {

  // NOTE: there's no UTF8 character for α hat (nor β hat), so we use â and ĉ for existential vars

  // types (A,B,C): 1 | α | â | ∀α.A | A→B
  sealed abstract class Type {
    /** Whether this type is a monotype. */
    def isMono :Boolean = true
    /** Returns whether `eV` is in the free variables of this type. */
    def containsFree (eV :TEVar) :Boolean
    /** Checks that this type is well-formed with respect to `ctx`, throws exception if not. */
    def checkWellFormed (implicit ctx :Context) :Unit = checkMalformed match {
      case Some(error) => fail(error)
      case None => // yay!
    }
    /** Returns whether this type is well-formed with respect to `ctx`. */
    def isWellFormed (implicit ctx :Context) :Boolean = !checkMalformed.isDefined
    /** Checks that this type is malformed with respect to `ctx`.
      * @return `Some(error)` if it is malformed, `None` if it is well-formed. */
    def checkMalformed (implicit ctx :Context) :Option[String]
  }
  case object TUnit extends Type {
    def containsFree (eV :TEVar) :Boolean = false
    def checkMalformed (implicit ctx :Context) = None
    override def toString = "()"
  }
  case class TUVar (name :String) extends Type with Note {
    def containsFree (eV :TEVar) :Boolean = false
    def checkMalformed (implicit ctx :Context) =
      if (!ctx.contains(this)) Some(s"Unbound type variable '$name'") else None
    override def toString = name
  }
  case class TEVar (name :String) extends Type with Note {
    def containsFree (eV :TEVar) :Boolean = eV == this
    def checkMalformed (implicit ctx :Context) =
      if (!ctx.contains(this) &&
          !solution(this).isDefined) Some(s"Unbound existential variable '$name'") else None
    override def toString = s"^$name"
  }
  case class TAll (uv :TUVar, tpe :Type) extends Type {
    override def isMono :Boolean = false
    def containsFree (eV :TEVar) :Boolean = tpe.containsFree(eV)
    def checkMalformed (implicit ctx :Context) = tpe.checkMalformed(uv :: ctx)
    override def toString = s"∀$uv. $tpe"
  }
  case class TArrow (arg :Type, res :Type) extends Type {
    override def isMono :Boolean = arg.isMono && res.isMono
    def containsFree (eV :TEVar) :Boolean = arg.containsFree(eV) || res.containsFree(eV)
    def checkMalformed (implicit ctx :Context) = arg.checkMalformed orElse res.checkMalformed
    override def toString = s"($arg -> $res)"
  }

  // terms (x): () | x | λx.e | e e | e:A
  sealed abstract trait Term
  case object XUnit extends Term {
    override def toString = "()"
  }
  case class XVar (name :String) extends Term {
    override def toString = name
  }
  case class XLambda (arg :XVar, exp :Term) extends Term {
    override def toString = s"(λ$arg.$exp)"
  }
  case class XApply (fun :Term, arg :Term) extends Term {
    override def toString = s"($fun $arg)"
  }
  case class XAnnot (exp :Term, tpe :Type) extends Term {
    override def toString = s"($exp : $tpe)"
  }

  // contexts (Γ,∆,Θ): · | Γ,α | Γ,x:A | Γ,â | Γ,â = τ | Γ,▶â
  sealed abstract trait Note
  // case class NUVar == TUVar
  case class NAssump (v :XVar, tpe :Type) extends Note {
    override def toString = s"$v : $tpe"
  }
  // case class NEVar == TEVar
  case class NSol (eV :TEVar, tpe :Type) extends Note {
    override def toString = s"$eV = $tpe"
  }
  case class NMark (eV :TEVar) extends Note {
    override def toString = s"▶$eV"
  }

  // a context is an ordered list of notes (note: the head of the list is the most recently added
  // note, which is opposite the lexical representation in the paper)
  type Context = List[Note]

  /** Looks up the assumption for `v` in `ctx`. */
  def assump (v :XVar)(implicit ctx :Context) :Option[Type] = {
    val assumps = ctx collect { case na @ NAssump(av, _) if (v == av) => na }
    assumps match {
      case Seq()   => None
      case Seq(na) => Some(na.tpe)
      case nas     => fail(s"Multiple types for '$v': $nas")
    }
  }

  /** Looks up the solution for `ev` in `ctx`. */
  def solution (eV :TEVar)(implicit ctx :Context) :Option[Type] = {
    val sols = ctx collect { case ns @ NSol(seV, _) if (eV == seV) => ns }
    sols match {
      case Seq()   => None
      case Seq(ns) => Some(ns.tpe)
      case nss     => fail(s"Multiple solutions for '$eV': $nss")
    }
  }

  /** Peels off the end of a context up to and including `note`. */
  def peel (ctx :Context, note :Note) :Context = (ctx dropWhile(_ != note)) match {
    case Nil    => Nil
    case h :: t => t
  }

  /** Splits `ctx` into the part after `note` and the part before. `note` itself is not included.
    * Recall that contexts list notes in reverse order, hence the `(post, pre)` return order.
    * If `note` is not in `ctx` then `None` is returned. */
  def split (ctx :Context, note :Note) :Option[(Context, Context)] = ctx.span(_ != note) match {
    case (post, Nil)  => None
    case (post, pre) => Some((post, pre.tail))
  }

  var nextEVar = 1
  def freshEVar (name :String) :TEVar = try TEVar(s"$name$nextEVar") finally nextEVar += 1

  // NOTE: to conserve monads, type errors are reported via exceptions
  def fail (msg :String) = throw new Exception(msg)

  /** Applies `ctx` to `tpe` (substituting existential vars for their solutions). */
  def apply (tpe :Type)(implicit ctx :Context) :Type = tpe match {
    case ev :TEVar     => solution(ev) map apply getOrElse ev
    case TArrow(a, b)  => TArrow(apply(a), apply(b))
    case TAll(uv, tpe) => TAll(uv, apply(tpe))
    case _ => tpe
  }

  /** Returns `inT` with `thatT` replaced by `thisT`. */
  def subst (thisT :TEVar, thatT :TUVar, inT :Type) :Type = inT match {
    case uv :TUVar     => if (thatT == uv) thisT else uv
    case TArrow(a, b)  => TArrow(subst(thisT, thatT, a), subst(thisT, thatT, b))
    case TAll(uv, tpe) => TAll(uv, subst(thisT, thatT, tpe))
    case _ /*TUnit, TEvar*/ => inT
  }

  /** Derives a subtyping relationship `tpeA <: tpeB` with input context `ctx`. See Figure 9.
    * @return the output context. */
  def subtype (tpeA :Type, tpeB :Type)(implicit ctx :Context) :Context = (tpeA, tpeB) match {
    // <:Unit :: Γ ⊢ 1 <: 1 ⊣ Γ
    case (TUnit, TUnit) => ctx // Γ

    // <:Var :: Γ[α] ⊢ α <: α ⊣ Γ[α]
    case (uva :TUVar, uvb :TUVar) if (uva == uvb) => ctx // Γ

    // <:Exvar :: Γ[â] ⊢ â <: â ⊣ Γ[â]
    case (eA :TEVar, eB :TEVar) if (eA == eB) =>
      if (ctx contains eA) ctx else fail(s"Unbound existential '$eA'") // Γ

    // <:→ :: Γ ⊢ A1→A2 <: B1→B2 ⊣ ∆
    case (TArrow(a1, a2), TArrow(b1, b2)) =>
      val theta = subtype(b1, a2) // Γ ⊢ B1 <: A1 ⊣ Θ
      subtype(apply(a2)(theta), apply(b2)(theta))(theta) // Θ ⊢ [Θ]A2 <: [Θ]B2 ⊣ ∆

    // <:∀L :: Γ ⊢ ∀α.A <: B ⊣ ∆
    case (TAll(uA, a), b) =>
      val eA = freshEVar("a")
      val eAMark = NMark(eA)
      val subCtx = eA :: eAMark :: ctx // Γ,▶â,â
      val deltaEtc = subtype(subst(eA, uA, a), b)(subCtx) // [â/α]A <: B ⊣ ∆,▶â,Θ
      peel(deltaEtc, eAMark) // ∆

    // <:∀R :: Γ ⊢ A <: ∀α.B ⊣ ∆
    case (a, TAll(uA, b)) =>
      val deltaEtc = subtype(a, b)(uA :: ctx) // Γ,α ⊢ A <: B ⊣ ∆,α,Θ
      peel(deltaEtc, uA) // ∆

    // <:InstantiateL :: Γ[â] ⊢ â <: A ⊣ ∆
    case (eA :TEVar, a) if (ctx.contains(eA) && !a.containsFree(eA)) =>
      trace(s"<:InstL $eA :=< $a")
      instantiateL(eA, a) // Γ[â] ⊢ â :=< A ⊣ ∆

    // <:InstantiateR :: Γ[â] ⊢ A <: â ⊣ ∆
    case (a, eA :TEVar) if (ctx.contains(eA) && !a.containsFree(eA)) =>
      trace(s"<:InstR $a :=< $eA")
      instantiateR(a, eA) // Γ[â] ⊢ A <: â ⊣ ∆

    case _ => fail(s"Type mismatch: expected '$tpeB', given: '$tpeA'")
  }

  /** Instantiates `eA` such that `eA <: a` in `ctx`. See Figure 10.
    * @return the output context. */
  def instantiateL (eA :TEVar, a :Type)(implicit ctx :Context) :Context = a match {
    // InstLSolve :: Γ,â,Γ′ ⊢ â :=< τ ⊣ Γ,â=τ,Γ′
    case a if (a.isMono && a.isWellFormed(peel(ctx, eA))) /* Γ ⊢ τ */ =>
      val Some((postCtx, preCtx)) = split(ctx, eA)
      trace(s"InstLSolve $eA :=< $a")
      postCtx ++ (NSol(eA, a) :: preCtx) // Γ,â=τ,Γ′

    // InstLReach :: Γ[â][ĉ] ⊢ â :=< ĉ ⊣ Γ[â][ĉ=â]
    case eC :TEVar if (peel(ctx, eC) contains eA) =>
      val Some((postCtx, preCtx)) = split(ctx, eC)
      trace(s"InstLReach $eA :=< $eC")
      postCtx ++ (NSol(eC, eA) :: preCtx) // Γ[â][ĉ=â]

    // InstLArr :: Γ[â] ⊢ â :=< A1 → A2 ⊣ ∆
    case TArrow(a1, a2) if (ctx contains eA) =>
      val Some((postCtx, preCtx)) = split(ctx, eA)
      val eA1 = freshEVar("a₁")
      val eA2 = freshEVar("a₂")
      val a1ctx = postCtx ++ (NSol(eA, TArrow(eA1, eA1)) :: eA1 :: eA2 :: preCtx)
      trace(s"InstLArr(1) $a1 :=< $eA1 in $a1ctx")
      val theta = instantiateR(a1, eA1)(a1ctx) // Γ[â₂,â₁,â=â₁→â2] ⊢ A1 :=< â₁ ⊣ Θ
      trace(s"InstRArr(2) $eA2 :=< ${apply(a2)(theta)} in $theta")
      instantiateL(eA2, apply(a2)(theta))(theta) // Θ ⊢ â₂ :=< [Θ]A2 ⊣ ∆

    // InstLAllR :: Γ[â] ⊢ â :=< ∀β.B ⊣ ∆
    case TAll(uB, b) if (ctx contains eA) =>
      trace(s"InstLAllR $eA :=< $b in ${uB :: ctx}")
      val deltaEtc = instantiateL(eA, b)(uB :: ctx) // Γ[â],β ⊢ â :=< B ⊣ ∆,β,∆′
      peel(deltaEtc, uB) // ∆

    case _ => fail(s"Failed to instantiate '$eA' to '$a'")
  }

  /** Instantiates `eA` such that `a <: eA` in `ctx`. See Figure 10.
    * @return the output context. */
  def instantiateR (a :Type, eA :TEVar)(implicit ctx :Context) :Context = a match {
    // InstRSolve :: Γ,â,Γ′ ⊢ τ :=< â ⊣ Γ,â=τ,Γ′
    case a if (a.isMono && a.isWellFormed(peel(ctx, eA))) /* Γ ⊢ τ */ =>
      val Some((postCtx, preCtx)) = split(ctx, eA)
      trace(s"InstRSolve $a :=< $eA")
      postCtx ++ (NSol(eA, a) :: preCtx) // Γ,â=τ,Γ′

    // InstRReach :: Γ[â][ĉ] ⊢ ĉ :=< â ⊣ Γ[â][ĉ=â]
    case eC :TEVar if (peel(ctx, eC) contains eA) =>
      val Some((postCtx, preCtx)) = split(ctx, eC)
      trace(s"InstRReach $eC :=< $eA")
      postCtx ++ (NSol(eC, eA) :: preCtx) // Γ[â][ĉ = â]

    // InstRArr :: Γ[â] ⊢ A1 → A2 :=< â ⊣ ∆
    case TArrow(a1, a2) if (ctx contains eA) =>
      val Some((postCtx, preCtx)) = split(ctx, eA)
      val eA1 = freshEVar("a₁")
      val eA2 = freshEVar("a₂")
      val a1ctx = postCtx ++ (NSol(eA, TArrow(eA1, eA1)) :: eA1 :: eA2 :: preCtx)
      trace(s"InstRArr(1) $eA1 :=< $a1 in $a1ctx")
      val theta = instantiateL(eA1, a1)(a1ctx) // Γ[â₂,â₁,â=â₁→â₂] ⊢ â₁ :=< A1 ⊣ Θ
      trace(s"InstRArr(2) ${apply(a2)(theta)} :=< $eA2 in $theta")
      instantiateR(apply(a2)(theta), eA2)(theta) // Θ ⊢ [Θ]A2 :=< â₂ ⊣ ∆

    // InstRAllL :: Γ[â],▶ĉ,ĉ ⊢ [ĉ/β]B :=< â ⊣ ∆,▶ĉ,∆′
    case TAll(uB, b) if (ctx contains eA) =>
      val eC = freshEVar("c")
      val instCtx = eC :: NMark(eC) :: ctx // Γ[â],▶ĉ,ĉ
      trace(s"InstRAllL [$eC/$uB]$b :=< $eA in $instCtx")
      val deltaEtc = instantiateR(subst(eC, uB, b), eA)(instCtx) // Γic ⊢ [ĉ/β]B :=< â ⊣ ∆,▶ĉ,∆′
      peel(deltaEtc, NMark(eC)) // ∆

    case _ => fail(s"Failed to instantiate '$a' to '$eA'\n (context: $ctx)")
  }

  /** Checks that `exp` has type `tpe` with input context `ctx`. See Figure 11.
    * @return the output context. */
  def check (exp :Term, tpe :Type)(implicit ctx :Context) :Context = (exp, tpe) match {
    // 1I :: ((), 1)
    case (XUnit, TUnit) => ctx // Γ

    // ->I :: (λx.e, A→B)
    case (XLambda(arg, exp), TArrow(argT, expT)) =>
      val argAssump = NAssump(arg, argT) // x:A
      trace(s"->I ($exp : $expT) in ${argAssump :: ctx}")
      val deltaEtc = check(exp, expT)(argAssump :: ctx) // Γ,x:A ⊢ e ⇐ B ⊣ ∆,x:A,Θ
      peel(deltaEtc, argAssump) // ∆

    // ∀I :: (e, ∀α.A)
    case (exp, TAll(uA, tpe)) =>
      val deltaEtc = check(exp, tpe)(uA :: ctx) // Γ,α ⊢ e ⇐ A ⊣ ∆,α,Θ
      peel(deltaEtc, uA) // ∆

    // Sub :: (e, B)
    case (exp, tpe) =>
      val (expType, theta) = infer(exp) // Γ ⊢ e ⇒ A ⊣ Θ
      trace(s"Sub ($exp : $expType) <: $tpe in $theta")
      subtype(apply(expType)(theta), apply(tpe)(theta))(theta) // Θ ⊢ [Θ]A <: [Θ]B ⊣ ∆
  }

  /** Infers a type for `exp` with input context `ctx`. See Figure 11.
    * @return the inferred type and the output context. */
  def infer (exp :Term)(implicit ctx :Context) :(Type, Context) = exp match {
    // 1I=> :: ()
    case XUnit => (TUnit, ctx) // 1 ⊣ Γ

    // Var :: x
    case v @ XVar(name) => assump(v) match {
      case Some(tpe) => (tpe, ctx) // A ⊣ Γ
      case None      => fail(s"No binding for variable '$name'")
    }

    // ->I=> :: λx.e
    case XLambda(arg, exp) =>
      val eA = freshEVar("a") // â
      val eC = freshEVar("c") // ĉ
      val assump = NAssump(arg, eA) // x:â
      val checkCtx = assump :: eC :: eA :: ctx // Γ,â,ĉ,x:â
      trace(s"->I=> ($exp : $eC) in $checkCtx")
      val checkedCtx = check(exp, eC)(checkCtx) // e ⇐ ĉ ⊣ ∆,x:â,Θ
      (TArrow(eA, eC), peel(checkedCtx, assump)) // â→ĉ ⊣ ∆

    // ->E :: (e1 e2)
    case XApply(fun, arg) =>
      val (funType, theta) = infer(fun) // e1 ⇒ A ⊣ Θ
      val reducedFun = apply(funType)(theta) // [Θ]A
      trace(s"->E inferApp $reducedFun $arg in $theta")
      inferApp(reducedFun, arg)(theta) // C ⊣ ∆

    // Anno: x:A
    case XAnnot(exp, tpe) =>
      tpe.checkWellFormed
      (tpe, check(exp, tpe)) // A ⊣ ∆
  }

  /** Infers the type of an application of a function of type `fun` to `exp`. See Figure 11.
    * @return the inferred type and the output context. */
  def inferApp (fun :Type, exp :Term)(implicit ctx :Context) :(Type, Context) = fun match {
    // ∀App
    case TAll(uv, tpe) =>
      val eA = freshEVar("a") // â
      val reduced = subst(eA, uv, tpe) // [â/α]A
      val appCtx = eA :: ctx // Γ,â
      trace(s"∀App $reduced ● $exp in $appCtx")
      inferApp(reduced, exp)(appCtx) // C ⊣ ∆
    // âApp
    case eA :TEVar =>
      val a1 = freshEVar("a₁") // â₁
      val a2 = freshEVar("a₂") // â₂
      val aArrow = TArrow(a1, a2) // â₁→â₂
      val Some((postCtx, preCtx)) = split(ctx, eA) // Γpre[â]post
      val checkCtx = postCtx ++ (
        NSol(eA, aArrow) :: a1 :: a2 :: preCtx) // Γpre[â₂,â₁,â=â₁→â₂]post
      trace(s"âApp $exp <= $a1 in $checkCtx")
      (a2, check(exp, a1)(checkCtx)) // â₂ ⊣ ∆
    // ->App
    case TArrow(argT, resT) => // A→C
      (resT, check(exp, argT)) // C ⊣ ∆
    case fun => fail(s"Cannot apply expr of type '$fun' to '$exp'")
  }

  /** Runs inference on `expr` and returns either its type or an error. */
  def inferExpr (expr :Term) :Either[String, Type] = try {
    nextEVar = 1 // makes error messages less arbitrary
    trace(s"inferExpr $expr")
    val (tpe, delta) = infer(expr)(Nil)
    Right(apply(tpe)(delta))
  } catch {
    case e :Exception => Left(e.getMessage)
  }

  val Trace = false
  private def trace (msg :String) = if (Trace) println(msg)
}
