package bidir

import org.junit.Assert._
import org.junit._

class BidirTest {
  import Bidir._

  @Test def testUnit () :Unit = {
    assertEquals(Right(TUnit), inferExpr(XUnit))
  }

  val xV = XVar("x")
  val yV = XVar("y")
  val fV = XVar("f")

  // id :: (forall a. a -> a)
  // id x = x
  val idExpr = XLambda(xV, xV)

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
  val hofExpr = XLambda(fV, XApply(fV, XUnit))

  @Test def testHOF () :Unit = {
    assertEquals(Right(TUnit), inferExpr(XApply(hofExpr, idExpr)))
  }

  @Test def testError () :Unit = {
    assertEquals(Left("Type mismatch: expected '(() -> ^a₂4)', given: '()'"),
                 inferExpr(XApply(hofExpr, XUnit)))
  }

  val aTV = TUVar("a")
  // hrf :: (forall a. (a -> a)) -> ()
  val hrfType = TArrow(TAll(aTV, TArrow(aTV, aTV)), TUnit)
  // hrf f = (f id) (f ())
  val hrfExpr = XLambda(fV, XApply(XApply(fV, idExpr), XApply(fV, XUnit)))

  @Test def testHigherRank () :Unit = {
    assertEquals(Left("Type mismatch: expected '(^a₂8 -> ^a₂8)', given: '()'"),
                 inferExpr(hrfExpr)) // fail: cannot infer higher-rank types
    assertEquals(Right(hrfType),
                 inferExpr(XAnnot(hrfExpr, hrfType))) // (hrf : hrfType)
    assertEquals(Right(TUnit),
                 inferExpr(XApply(XAnnot(hrfExpr, hrfType), idExpr))) // ((hrf : hrfType) id)
  }
}
