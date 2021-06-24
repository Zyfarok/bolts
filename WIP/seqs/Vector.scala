import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.proof._
import scala.collection.immutable

object Vector {
    final val MAX_WIDTH: BigInt = 32

    abstract sealed class Vector {
        @pure
        lazy val height: BigInt = {
            this match {
                case VectorLeaf(xs) => BigInt(0)
                case VectorNode(v, vs) => 1 + v.height
            }
        } ensuring(0 <= _)

        lazy val width: BigInt = {
            this match {
                case VectorLeaf(xs) => xs.length
                case VectorNode(v, vs) => 1 + vs.length
            }
        } ensuring(res => 0 <= res && res <= MAX_WIDTH)

        lazy val size: BigInt = {
            decreases(height * MAX_WIDTH + width)
            this match {
                case VectorLeaf(xs) => xs.length
                case vn @ VectorNode(v, vs) => v.size + vn.tail.size
            }
        } ensuring((res: BigInt) => res == this.toList.length)

        def toList: List[BigInt] = {
            decreases(height * MAX_WIDTH + width)
            this match {
                case VectorLeaf(xs) => xs
                case vn @ VectorNode(v, vs) => v.toList ++ vn.tail.toList
            }
        }

        def apply(i: BigInt): BigInt = {
            require(0 <= i && i < size)
            decreases((height * MAX_WIDTH + width))
            this match {
                case VectorLeaf(xs) => xs(i)
                case vn @ VectorNode(v, vs) => {
                    ListSpecs.appendIndex[BigInt](v.toList, vn.tail.toList, i)
                    if(i < v.size) v(i) else vn.tail(i - v.size)
                }
            }
        } ensuring(_ == this.toList(i))

        def concat(that: Vector): Vector = {
            if (this.height == that.height) {
                if(this.width + that.width > MAX_WIDTH) {
                    VectorNode(this, List(that)) // Balance ?
                } else {
                    (this, that) match {
                        case (a: VectorLeaf, b: VectorLeaf) => VectorLeaf(a.xs ++ b.xs)
                        case (a: VectorNode, b: VectorNode) => VectorNode(a.v, a.vs ++ (b.v :: b.vs))
                    }
                }
            } else {
                ???
            }
        }

        def tryConcat(that: Vector): List[Vector] = {
            if(this.height == that.height) {
                if(this.width + that.width > MAX_WIDTH) {
                    List(this, that) // Balance ?
                } else {
                    List((this, that) match {
                        case (a: VectorLeaf, b: VectorLeaf) => VectorLeaf(a.xs ++ b.xs)
                        case (a: VectorNode, b: VectorNode) => VectorNode(a.v, a.vs ++ (b.v :: b.vs))
                    })
                }
            } else if (this.height < that.height) {
                val l = this.tryConcat(that.v)
                val l2 = 
                concat(that.tail)
            } else {
                assert(that.height < this.height)
                List()
            }
        }

        // def pushBack(e: BigInt): Vector = {
        //     this match {
        //         case VectorLeaf(arr) => {
        //             assert(this.height == 0)
        //             assert(VectorLeaf(List(e)).height == 0)
        //             if(size < MAX_WIDTH) VectorLeaf(arr :+ e) else VectorNode(this, List(VectorLeaf(List(e))))
        //         }
        //         case vn @ VectorNode(v, vs) => {
        //             ???
        //         }
        //     }
        // }
    }
    
    case class VectorLeaf(xs: List[BigInt]) extends Vector {
        require(xs.length <= MAX_WIDTH)
    }
    
    case class VectorNode(v: Vector, vs: List[Vector]) extends Vector {
        require(vs.forall(x => x.height == v.height) && vs.length < MAX_WIDTH)

        def tail: Vector = {
            vs match {
                case Cons(h,t) => {
                    assert(vs.forall(x => x.height == v.height))
                    assert(t.forall(x => x.height == v.height))
                    assert(v.height == vs.head.height)
                    assert(forallEqualLemma(t, v, vs.head))
                    assert(t.forall(x => x.height == vs.head.height))
                    VectorNode(vs.head, vs.tail)
                }
                case Nil() => {
                    VectorLeaf(List.empty[BigInt])
                }
            }
        }
    }

    def forallEqualLemma(@induct vs: List[Vector], a: Vector, b: Vector): Boolean = {
        require(a.height == b.height && vs.forall(x => x.height == a.height))
        vs.forall(x => x.height == b.height)
    }.holds
}