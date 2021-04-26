import stainless.collection._

object AdtInvarTimeout {
    case class LowerBoundedList(lowerBound: BigInt, list: List[BigInt]) {
        require(list.forall(x => lowerBound < x))

        def changeBound(newBound: BigInt): LowerBoundedList = {
            require(newBound < lowerBound)
            LowerBoundedList(newBound, list)
        }
    }
}