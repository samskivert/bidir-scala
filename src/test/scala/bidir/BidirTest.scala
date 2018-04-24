package bidir

import org.junit.Assert._
import org.junit._

class BidirTest {
  import Bidir._

  @Test def testUnit () :Unit = {
    assertEquals(Right(TUnit), inferExpr(XUnit))
  }

  def xV = XVar("x")
  def yV = XVar("y")
  def fV = XVar("f")
  def aTV = TUVar("a")

  // id :: (forall a. a -> a)
  def idType = TAll(aTV, TArrow(aTV, aTV))
  // id x = x
  def idExpr = XLambda(xV, xV)

  @Test def testSplit () :Unit = {
    val aUV = TUVar("a")
    val bEV = TEVar("b")
    val xVAssump = NAssump(xV, TUnit)
    val ctx = aUV :: bEV :: xVAssump :: Nil
    val Some((post, pre)) = split(ctx, bEV)
    assertEquals(aUV :: Nil, post)
    assertEquals(xVAssump :: Nil, pre)
  }

  @Test def testIdent () :Unit = {
    assertEquals(Right(TArrow(TEVar("a1"), TEVar("a1"))), inferExpr(idExpr))
    assertEquals(Right(TUnit), inferExpr(XApply(idExpr, XUnit)))
  }

  // hof :: (forall a. () -> a) -> a
  // hof f = f ()
  def hofUnitExpr = XLambda(fV, XApply(fV, XUnit))
  // hof :: (forall a. Bool -> a) -> a
  // hof f = f true
  def hofBoolExpr = XLambda(fV, XApply(fV, XTrue))

  @Test def testHOF () :Unit = {
    assertEquals(Right(TUnit), inferExpr(XApply(hofUnitExpr, idExpr)))
    assertEquals(Right(TBool), inferExpr(XApply(hofBoolExpr, idExpr)))
  }

  @Test def testError () :Unit = {
    assertEquals(Left("Type mismatch: expected '(() -> ^a₂4)', given: '()'"),
                 inferExpr(XApply(hofUnitExpr, XUnit)))
  }

  // hrf :: (forall a. (a -> a)) -> ()
  def hrfType = TArrow(TAll(aTV, TArrow(aTV, aTV)), TUnit)
  // hrf f = (f id) (f ())
  def hrfExpr = XLambda(fV, XApply(XApply(fV, idExpr), XApply(fV, XUnit)))

  @Test def testHigherRank () :Unit = {
    assertEquals(Left("Type mismatch: expected '(^a₂8 -> ^a₂8)', given: '()'"),
                 inferExpr(hrfExpr)) // fail: cannot infer higher-rank types
    assertEquals(Right(hrfType),
                 inferExpr(XAnnot(hrfExpr, hrfType))) // (hrf : hrfType)
    assertEquals(Right(TUnit),
                 inferExpr(XApply(XAnnot(hrfExpr, hrfType), idExpr))) // ((hrf : hrfType) id)
  }

  @Test def testLet () :Unit = {
    // let y = (λx.x) false in y
    assertEquals(Right(TBool), inferExpr(XLet(yV, XApply(idExpr, XFalse), yV)))
    // let y = (λx.x) in (y false)
    assertEquals(Right(TBool), inferExpr(XLet(yV, idExpr, XApply(yV, XFalse))))
    // let f = (λx.x) in let y = (λx.x) in ((f y) false)
    val yLetE = XLet(yV, idExpr, XApply(XApply(fV, yV), XFalse))
    assertEquals(Right(TBool), inferExpr(XLet(fV, idExpr, yLetE)))
    // let f = (λx.x) : (forall a. a -> a) in let y = (λx.x) in ((f y) (f false))
    val yLetU = XLet(yV, idExpr, XApply(XApply(fV, yV), XApply(fV, XFalse)))
    assertEquals(Right(TBool), inferExpr(XLet(fV, XAnnot(idExpr, idType), yLetU)))
  }

  @Test def testIf () :Unit = {
    assertEquals(Right(TBool), inferExpr(XIf(XFalse, XFalse, XTrue)))
    assertEquals(Right(TUnit), inferExpr(XIf(XIf(XFalse, XFalse, XTrue), XUnit, XUnit)))
    assertEquals(Right(TBool), inferExpr(XIf(XFalse, XApply(idExpr, XFalse), XTrue)))
    assertEquals(Right(TBool), inferExpr(XIf(XFalse, XTrue, XApply(idExpr, XFalse))))
  }
}
