/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._
import stainless.lang.StaticChecks._
import stainless.collection._

object BST {
  sealed abstract class Tree {
    def content: Set[BigInt] = this match {
      case Node(l, v, r) => l.content ++ Set(v) ++ r.content
      case Leaf => Set.empty[BigInt]
    }

    lazy val size: BigInt = (this match {
      case Node(left, value, right) => left.size + right.size + 1
      case Leaf => BigInt(0)
    }) ensuring(res => 0 <= res)
    // ensuring(res => res == content.size)

    def insert(value: BigInt): Node = {
      decreases(size*2)
      this match {
        case Leaf => Node(Leaf, value, Leaf)
        case Node(l, v, r) => (if (v < value) {
          BSTSpecs.insertValidRight(r, value, v)
          Node(l, v, r.insert(value))
        } else if (value < v) {
          BSTSpecs.insertValidLeft(l, value, v)
          Node(l.insert(value), v, r)
        } else {
          Node(l, v, r)
        })
      }
    } ensuring(res => res.content == this.content ++ Set(value))

    def forall(p: BigInt => Boolean): Boolean = {
      this match {
        case Node(left, value, right) => p(value) && left.forall(p) && right.forall(p)
        case Leaf => true
      }
    } //ensuring(_ == content.forall(p))

    def leftFrom(rLimit: BigInt): Tree = {
      decreases(size)
      this match {
        case Node(left, value, right) => if(value < rLimit) {
          assert(BSTSpecs.validRight(right, value))
          assert(BSTSpecs.validRight(right.leftFrom(rLimit),value))
          Node(left, value, right.leftFrom(rLimit))
        } else {
          left.leftFrom(rLimit)
        }
        case Leaf => Leaf
      }
    }

    def rightFrom(lLimit: BigInt): Tree = {
      decreases(size)
      this match {
        case Node(left, value, right) => if(lLimit < value) {
          assert(BSTSpecs.validLeft(left.rightFrom(lLimit),value))
          //assert(forall((x:BigInt) => (left.content.contains(x) ==> this.content.contains(x))))
          Node(left.rightFrom(lLimit), value, right)
        } else {
          //assert(forall((x:BigInt) => (right.content.contains(x) ==> this.content.contains(x))))
          right.rightFrom(lLimit)
        }
        case Leaf => Leaf
      }
    } 
    //ensuring(res => forall((x:BigInt) => (res.content.contains(x) ==> this.content.contains(x))))

    // def remove(value: BigInt): Node = {
    //   this match {
    //     case Leaf => Leaf
    //     case Node(left, value, right) => (if (v < value) {
    //       Node(l, v, r.remove(value))
    //     } else if (value < v) {
    //       Node(l.remove(value), v, r)
    //     } else {
    //       // TODO...
    //     })
    //   }
    // }
  }

  case class Node(left: Tree, value: BigInt, right: Tree) extends Tree {
    require(BSTSpecs.validLeft(left, value) && BSTSpecs.validRight(right, value))
  }
  case object Leaf extends Tree

  val empty: Tree = Leaf

  def createRoot(v: BigInt): Node = {
    Node(Leaf, v, Leaf)
  } ensuring (_.content == Set(v))

  // def isBST(tree: Tree) : Boolean = tree match {
  //   case Leaf() => true
  //   case Node(left, v, right) => {
  //     isBST(left) && isBST(right) &&
  //     forall((x:BigInt) => (content(left).contains(x) ==> x < v)) &&
  //     forall((x:BigInt) => (content(right).contains(x) ==> v < x))
  //   }
  // }
}

import BST._

object BSTSpecs {
  def validLeft(tree: Tree, rLimit: BigInt) : Boolean = {
    decreases(tree.size*2)
    tree match {
      case Node(l, v, r) =>
        (v < rLimit
        && validLeft(l, v)
        && validMid(r, v, rLimit))
      case Leaf => true
    }
  } //ensuring(_ ==> tree.forall(_ < rLimit))

  def validRight(tree: Tree, lLimit: BigInt) : Boolean = {
    decreases(tree.size*2)
    tree match {
      case Node(l, v, r) =>
        (lLimit < v
        && validMid(l, lLimit, v)
        && validRight(r, v))
      case Leaf => true
    }
  } //ensuring(_ ==> tree.forall(lLimit < _))

  def validMid(tree: Tree, lLimit: BigInt, rLimit: BigInt) : Boolean = {
    decreases(tree.size*2 + 1)
    tree match {
      case Node(l, v, r) =>
        (lLimit < v && v < rLimit
        && validMid(l, lLimit, v)
        && validMid(r, v, rLimit))
      case Leaf => true
    }
  } ensuring(_ ==> (validLeft(tree, rLimit) && validRight(tree, lLimit)))

  def insertValidLeft(tree: Tree, value: BigInt, rLimit: BigInt): Boolean = {
    require(validLeft(tree, rLimit) && value < rLimit)
    decreases(tree.size*2 + 1)
    tree match {
      case Node(l, v, r) if (v < value) => insertValidMid(r, value, v, rLimit)
      case _ => ()
    }
    validLeft(tree.insert(value), rLimit)
  }.holds

  def insertValidRight(tree: Tree, value: BigInt, lLimit: BigInt): Boolean = {
    require(validRight(tree, lLimit) && lLimit < value)
    decreases(tree.size*2 + 1)
    tree match {
      case Node(l, v, r) if (value < v) => insertValidMid(l, value, lLimit, v)
      case _ => ()
    }
    validRight(tree.insert(value), lLimit)
  }.holds

  def insertValidMid(tree: Tree, value: BigInt, lLimit: BigInt, rLimit: BigInt): Boolean = {
    require(validMid(tree, lLimit, rLimit) && lLimit < value && value < rLimit)
    decreases(tree.size*2 + 2)
    tree match {
      case Node(l, v, r) if (v < value) => insertValidMid(r, value, v, rLimit)
      case Node(l, v, r) if (value < v) => insertValidMid(l, value, lLimit, v)
      case _ => ()
    }
    validMid(tree.insert(value), lLimit, rLimit)
  }.holds

  def leftSound(tree: Tree, rLimit: BigInt): Boolean = {
    require(validLeft(tree, rLimit))
    tree match {
      case Node(left, value, right) => {
        validLefter(left, value, rLimit)
        leftSound(left, rLimit) && leftSound(right, rLimit)
      }
      case _ => ()
    }
    forall((x:BigInt) => (tree.content.contains(x) ==> x < rLimit))
  }.holds

  def rightSound(tree: Tree, lLimit: BigInt): Boolean = {
    require(validRight(tree, lLimit))
    tree match {
      case Node(left, value, right) => {
        validRighter(right, value, lLimit)
        rightSound(left, lLimit) && rightSound(right, lLimit)
      }
      case _ => ()
    }
    forall((x:BigInt) => (tree.content.contains(x) ==> lLimit < x))
  }.holds

  def validRighter(tree: Tree, lLimit: BigInt, x: BigInt): Boolean = {
    require(validRight(tree, lLimit) && x < lLimit)
    tree match {
      case Node(left, value, right) => {
        validRighter(left, lLimit, x)
        validRighter(right, value, x)
      }
      case Leaf => ()
    }
    validRight(tree, x)
  }.holds

  def validLefter(tree: Tree, rLimit: BigInt, x: BigInt): Boolean = {
    require(validLeft(tree, rLimit) && rLimit < x)
    tree match {
      case Node(left, value, right) => {
        validLefter(left, value, x)
        validLefter(right, rLimit, x)
      }
      case Leaf => ()
    }
    validLeft(tree, x)
  }.holds
}