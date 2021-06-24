# Formaly verified data-structures in stainless

Author : Clément Burgelin (Sciper : 249954)

Note : the file names and line numbers are clickable and redirect to the code.

## 1- Motivation and project planning

### Motivation

Last semester, as final project for the formal verification class, I suggested to my group to try working on formaly verifying safety and liveness properties on Transactionnal Memory (TM) algorithms. This is the project we chose to do and we tried to implement and formaly verify a TM algorithm by using a model of simulated concurency. We were originaly working with Dafny but due to multiple bugs encountered with it, we switched and rewrote the algorithm in stainless instead. As we were trying to fulfill our objectives, we were slown down by the lack of fully formaly proven data-structures in stainless. In particular, the Set and Map provided in stainless are internally using the implementations from scala and they provide a limited interface and a limited set of properties that don't seem to be formaly verified. ListMap is an alternative Map implementation written in stainless and formaly proven but it also has a limited interface and set of provided properties.

From those observations, I thought that creating useful fully formaly verified data-structures in stainless could be beneficial to other projects, which lead to this project.

### The original plan (too optimistic)

The original plan was :
- to checkout and possibly improve previously implemented collection (Heaps, BinarySearchTree, AssociativeList, RedBlackTree, Trees1, Stream, ListOperations/Monads, IntSet, ...)
- to double-check the provided properties, and extend the interface and properties available for Set, Map/ListMap and List.
- to implement new useful formaly proven data-structures (ListSet, Vector, ArrayList, Trees, Matrices, Graphs, ...)

This plan was way too optimistic as it takes a lot more time than I thought to formally verify even a single collection, at least with how experimented I am with stainless, and a lot of unexpected difficulties came in. The plan being too optimistic was not a problem though as it was mostly there as a list of things that could be done so that I could pick something from the list as soon as I finished something.

### Project history

At the very start of the project, I started reviewing existing collections for the first 2 weeks and trying to figure out what should be improved or created. I've coded a few little things that are not really worth digging into and after some discussion, it was decided to go with an implementation of BinarySearchTree and from week 3 to week 7, I worked on extending the existing implementation of RedBlackTree.

After implementing the fully formaly verified RedBlackTree, starting from week 7, I stared working on both an ArrayList and an immutable Vector implentations in stainless. The implementations of those two were then interupted on week 9 to start focussing on a "BitInteger" implementation from week 10 until week 15 with the end of the project.


## 2- Red-Black Tree

The final implementation of this part is contained in [RedBlackTree.scala](https://github.com/epfl-lara/bolts/blob/7e59e71b2d675e5a882feec9d2718f6b39edc5f2/data-structures/trees/RedBlackTree.scala) and [StrictlyOrderedList.scala](https://github.com/epfl-lara/bolts/blob/7e59e71b2d675e5a882feec9d2718f6b39edc5f2/data-structures/trees/StrictlyOrderedList.scala), both present in the [epfl-lara/bolts](https://github.com/epfl-lara/bolts) github repository. I used `smt-z3` for the verification with a timeout of 5 and default settings.

### Definition

A binary search tree (BST) is an implementation of a set or map. A BST is made of lodes and leaves, and one of them is the root. Nodes contain a key (and the associated value if it represents a Map), and a reference to two children called left and right sub-trees. Leaves simply represent empty trees or sub-trees. A tree or sub-tree is a leaf or node (called the root node if it is a tree). A BST has the property that all keys of the left sub-tree of a node are strictly smaller than the key of the node, and all keys found on the right sub-tree of a node are strictly bigger than the key of the node.

BSTs provide efficient implementations of `contains`, `insert` and `delete` operation as long as they are balanced. Various forms of BST exists that solve the balancing problem differently, and the red-black tree (later called red-black tree) is one of them.

A valid red-black tree is defined as follows :
- The root node should be colored black.
- The root node should itself be a valid "red-black sub-tree".

A valid red-black sub-tree is defined as follows :
- The sub-tree is a valid BST (valid ordering of keys, as defined previously).
- Each node or leaf are colored red (R) or black (B).
- All leaves should be black.
- Red nodes should have black children.
- The black-height, defined as "amount of black nodes you go through to reach a leaf" should be the same on the left and right subtree.
- The children of a node should be valid red-black sub-trees.

While red-black trees like other BST tree can be used to represent sets or maps of any objects as long as an ordering of keys is provided, we decided to limit to red-black trees representing a set of BigInt to simplify the implementation.

### Starting point

There was already an [existing RedBlackTree implementation](https://github.com/epfl-lara/stainless/blob/ad0e6b5c984265eb4585adf3ef5d0d905b49983c/frontends/benchmarks/verification/valid/RedBlackTree.scala) in the stainless repo. The existing implementation provides `add` (insertion), but only the conservation of the balancing properties during insertion and the equivalence with Set insertion are proven.

The objective was to implement `remove` (deletion) and `contains`, and prove conservation of all properties (ordering and balancing) on both `add` (insertion) and `remove` (deletion) as well as equivalence of all three operations on RedBlackTrees to their equivalent on some alternative(s) datastructure(s).

### StrictlyOrderedList

In order to prove the conservation of the BST ordering property, we decided to follow the idea of paper \[1\] to provide equivalence of the BST to a strictly ordered List (in ascending order).
Even though the stainless implementation of List has a lot a properties available, a few properties on "strictly ordered list" had to be proven.
In [StrictlyOrderedList.scala](https://github.com/epfl-lara/bolts/blob/7e59e71b2d675e5a882feec9d2718f6b39edc5f2/data-structures/trees/StrictlyOrderedList.scala), we first define `isInorder` ([#L24](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/data-structures/trees/StrictlyOrderedList.scala#L24)) which is the property that defines a strictly ordered list and then provide formaly proven properties applying to those strictly ordered list :
- If a list is strictly ordered, it's subparts are also strictly ordered
- If you concatenate two strictly ordered lists such that the last element of the left one is strictly smaller that the first element of the right one, then the concatenation is also strictly ordered
- If `e` is bigger or equal than some element y of a strictly ordered list `xs ++ y :: ys`, then `e` can not be contained in `xs`.
- If `e` is smaller or equal than some element y of a strictly ordered list `xs ++ y :: ys`, then `e` can not be contained in `ys`.

Also, we provide `inorderInsert` ([#L99](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/data-structures/trees/StrictlyOrderedList.scala#L99)) and `deleteFirst` ([#L140](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/data-structures/trees/StrictlyOrderedList.scala#L140)) which try to respectively insert or delete the provided element from the list while conservating strict ordering, along with some properties on those functions.

### BST validity (ordering)

In [RedBlackTree.scala](https://github.com/epfl-lara/bolts/blob/7e59e71b2d675e5a882feec9d2718f6b39edc5f2/data-structures/trees/RedBlackTree.scala), a conversion of a RedBlackTree to a list was defined in `toList` ([#L42](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/data-structures/trees/RedBlackTree.scala#L42)) as a simple recursive concatenation of lists.
Then, validity of the BST formed by the RedBlackTree was defined in `isBST` ([#L132](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/data-structures/trees/RedBlackTree.scala#L132)) as a simple call to `isInorder` on the list obtain from `toList`.

From that, proving that `add(tree, x)` ([#L486](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/data-structures/trees/RedBlackTree.scala#L486)) and `remove(tree, x)` ([#L644](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/data-structures/trees/RedBlackTree.scala#L644)) conserves the BST ordering is equivalent to proving that the result of `res.toList` (with res being the value returned) is respectively equal to `inorderInsert(tree.toList, x)` for `add` and `deleteFirst(tree.toList, x)` for `remove`. This is proven recursively on the intermediate unbalanced tree produced in the recursive function `ins` ([#L446](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/data-structures/trees/RedBlackTree.scala#L446)) for insertion and `del` ([#L584](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/data-structures/trees/RedBlackTree.scala#L584)) for deletion, and using the fact that the balancing operations like `balance` ([#L245](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/data-structures/trees/RedBlackTree.scala#L245)) and `rotate` ([#L308](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/data-structures/trees/RedBlackTree.scala#L308)) do not change the list produced by `toList`, which was proven using associativy properties defined in the [RedBlackTreeSpecs](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/data-structures/trees/RedBlackTree.scala#L653) object.


### deletion implementation and balancing

While insertion was already implemented and is quite simple, deletion in red-black trees is much more complicated. To implement deletion, I chose to use the "Double-Black" abstraction as seen in paper \[2\].

Adding the "Double-black" color (considered invalid in a red-black tree and only used for a temporary subtree) allows to express the conservation of black-height and black balancing in an elegent way. In `del` ([#L584](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/data-structures/trees/RedBlackTree.scala#L584)) we replace the value we delete with the maximum of the left subtree using `popMax` ([#L495](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/data-structures/trees/RedBlackTree.scala#L495)) or with the minimum of the right subtree using `popMin` ([#L541](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/data-structures/trees/RedBlackTree.scala#L541)). These pop functions conserve the black-height, using the Double-black color if necessary. To eliminate the double-blacks or move them up to the top of the three, the `rotate` ([#L308](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/data-structures/trees/RedBlackTree.scala#L308)) function is used. If the double-black reached the top without being eliminated yet, we can just color the root node in black again which reduces the height of the three by one. I recommend you to read paper \[2\] for more details about the algorithm.

Since deletion was not implemented before, both the conservation of the BST ordering properties and of the balacing properties had to be proven, which was done in the body of the function themselves to avoid code duplication.

### Results

The results is a fully formaly proven red-black tree with insertion and deletion. I won't detail the formal verification of `contains` ([#L57](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/data-structures/trees/RedBlackTree.scala#L57)) as it is much simpler than addition and deletion.

## 3- Vector

The data-structure I wanted to implement is a immutable Vector similar to the ones implemented in the Scala library. Vectors are sequences like Lists but they provide `O(log(n))` access time and concatenations. Their structures is quite similar to trees, and they have the same problematic of requiring to ensure balancing properties. A vector is a sequence represented as a tree of nodes and leaves, each node being a bounded list of references to sub-vectors and each leaf being a list of values.

The idea I wanted to use for the proof is similar to the one used for BST properties of red-black trees : proove equivalence of a Vector to a List.

While I did start the implementation of a Vector, I didn't commit any of the code as I didn't reach any interesting parts and only the very beginning was done. I stopped working on Vectors in order to concentrate my work on ArrayList and then BitIntegers as described bellow.

## 4- ArrayList

The final implementation of this part is contained in [ArrayList.scala](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/seqs/ArrayList.scala) present in the [epfl-lara/bolts](https://github.com/epfl-lara/bolts) github repository. I used `smt-z3` for the verification with a timeout of 5 and default settings.

### Definition

ArrayList are sequences of values that uses an Array internaly and apply automatic resizing of this array when necessary.
They provide constant time accesses and updates, and amotized constant time pop and pushback.
They provide the benefits of Array while removing the need of handling the size.

The idea here was to implement such ArrayList using the Arrays provided by stainless and by proving their equivalence to List (except for mutability).

### Array to list

The first part of this is the `toList` ([#L82](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/seqs/ArrayList.scala#L82)) function which converts an ArrayList to a List using `arrayPortionToList` ([#L28](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/seqs/ArrayList.scala#L28)).

As I wanted to prove that the list returned was of the same size as the ArrayList, I came into the first problem : stainless Lists use BigInt for size and indices while Arrays uses Int, and there is no way to convert one into the other or compare one with the other in stainless currently. As a temporary solution, I implemented `listLenght` ([#L13](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/seqs/ArrayList.scala#L13)), an alternative to `List.lenght` that uses Int instead of BigInt. Here, buffer overflows shouldn't happen as the list generated from an Array can't be longer than `Int.MaxInt` since array themselves can't exceed this lenght but since there's no way to share that information with the solver here, I had to create a special case for overflows.

### Array pushback

Then, I implemented one of the most basic form of insertions on ArrayLists : `pushBack` ([#L86](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/seqs/ArrayList.scala#L86)).
In this function, if the Array is not full, you just have to update the corresponding value in the array, and increment the lenght. If the Array is already full, you have to create a new Array with bigger capacity (here I double the previous capacity) and copy the previous values into the Array. To ensure equivalence with list "pushback", we need first need to proove that the copied portition of the new Array is the same as the previous Array, and this is what is done in `arrayCopy` ([#L41](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/seqs/ArrayList.scala#L41)).

### Results

The result is a very incomplete and partially proven ArrayList. I could have continued further but prefered to focus on the implementation of BitIntegers first as they should allow an elegent way to compare BigInts and Ints.


## 5- BitInteger

The final implementation of this part is contained in the [BitInteger.scala](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/int/BitInteger.scala) and [BitIntegerInt.scala](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/int/BitIntegerInt.scala), both present in the  [epfl-lara/bolts](https://github.com/epfl-lara/bolts) github repository. I used `no-inc:smt-z3` for the (incomplete) verification with a timeout of 5 and the `--strict-arithmetic=false` settings.

### Definition

A BitInteger is a List of bits (Booleans) of variable lenght that represent an integer, similar to the bit-reprensations we can find in processors. Since the list size is unbounded, any integer can in theory be represented.

Two forms are defined in [BitInteger.scala](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/int/BitInteger.scala) :
- `UnsignedBitInteger` ([#L12](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/int/BitInteger.scala#L12)) represent a positive integer, starting with the most significant bit.
- `SignedBitInteger` ([#L34](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/int/BitInteger.scala#L34)) represent a signed integer, represented in two's complement representation, starting from the most significant bit (which can be interpreted as the sign).

The objective here is to define conversion from and to BigInt, and from and to Int, in order to be able to use them for conversions and comparisons in other proofs (like in ArrayList).

### BitIntTools

In the `BigIntTools` ([#L64](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/int/BitInteger.scala#L64)) I wrote various helper functions and properties related to powers of 2 and BigInts. Most notably :
- `pow2(n)` computes "2 power `n`" recursively using multiplication by two.
- `pow2Order` applies the strictly monotonic property of `pow2`.
- `unsignedBitSize(x)` returns the amount of bits required to store a positive BigInt `x` in an `UnsignedBitInteger`.
- `bitSize(x)` returns the amount of bits required to store a BigInt `x` in a `SignedBitInteger`.

### converting BitIntegers to their BigInt value

The `toBigInt` ([#L149](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/int/BitInteger.scala#L149)) function is defined for UnsignedBitInteger and SignedBitInteger.

It is pretty simple as it simply sums the power of 2 value of each "True" bit, the only difference in SignedBitInteger compared to UnsignedBitInteger being that the bit is accounted as negative. From the poscondition of toBigInt for UnsignedBitInteger, the sign of toBigInt for SignedBitInteger is easily proven.

### creating BitIntegers from BigInt

This part is where the complexity begins.

`unsignedFrom` ([#L279](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/int/BitInteger.scala#L279)) creates an `UnsignedBitInteger` from a `BigInt`. To prove the correctness it's correctness we want to prove that `toBigInt` called with the output of `unsignedFrom` gives back the original BigInt.

The bits are constructed recursively from the least significant one using the quotien and remainder of the euclidian division by 2. The proof is not very complicated, as it simply uses an invariant that remains true as we accumulate the bits one by one, but requires a bit of intermediate assertions to guide the solver.

`from` ([#L289](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/int/BitInteger.scala#L289)) creates a `SignedBitInteger` from a `BigInt`. For positive numbers, we simply call `unsignedFrom` and add a False bit to preceed it, but for negative numbers, this is a bit more complicated.

For a negative numbers `x`, we first find the biggest negative power of 2 that is smaller or equal to `x`, substract it to `x` to obtain a positive number and convert this positive number using `unsignedFrom`. We then extend the result with enough zeroes such that the sign bit can be added with the correct negative power of 2 value.

The proof for the negative case is almost fully automatic as it reuses properties of `unsignedFrom` and `bitExtension` ([#L173](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/int/BitInteger.scala#L173)).

### Prooving bijections with BigInts

Complete bijection between "shrinked" `UnsignedBitInteger` and positive BigInts and with "shrinked" `SignedBitInteger` and all BigInts is proven in `unsignedSound`, `unsignedSound2`, `signedSound` and `signedSound2` ([#L554](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/int/BitInteger.scala#L554)).

They use the `equal` functions defined for both `UnsignedBitInteger` ([#L391](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/int/BitInteger.scala#L391)) and `SignedBitInteger` ([#L453](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/int/BitInteger.scala#L453)) which defines equality in a bitwise fashion and its equivalence with the equality on BigInts.

"shrinked" `UnsignedBitInteger` and `SignedBitInteger` are defined as having the minimum size required to represent some number.
They can be obtained from "unshrinked" BitIntegers using the `shrinking` functions ([#L195](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/int/BitInteger.scala#L195))

### BitInts and Ints

In [BitIntegerInt.scala](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/int/BitIntegerInt.scala), I tried to provide conversion and proove equivalence between BitIntegers of limited lenght (31 for unsigned and 32 for signed) with Intgers.

The `IntTools` object contains equivalents of the functions in `BigIntTools` using Ints instead. Some additionnal function are added to counter the maximum int limitation.

Unfortunately I faced a lot of problems due to overflows which made the proofs much more complicated than with BigInts, even though I used the `--strict-arithmetic=false` settings. For example, I had to create a `multCongr` ([#L53](https://github.com/epfl-lara/bolts/blob/fd2eb5d3690a383e942cd90a10e90d3fbdf117f2/WIP/int/BitIntegerInt.scala#L53)) function to be able to substitute a factor with an expression that is equal to it.

Due to that, the file is incomplete and conversions with Int are not completed yet.

## 5- Conclusion

Unfortunately, only `RedBlackTree.scala` was fully completed. Stainless is a great tool but it still faces many limitation, like the random crashes you can encounter when dealing with amount of proofs and the unexpected behaviors of Ints.

## 6- Sources
- \[1\] - Nipkow T. (2016) Automatic Functional Correctness Proofs for Functional Search Trees. In: Blanchette J., Merz S. (eds) Interactive Theorem Proving. ITP 2016. Lecture Notes in Computer Science, vol 9807. Springer, Cham. https://doi.org/10.1007/978-3-319-43144-4_19 
- \[2\] - GERMANE, K., & MIGHT, M. (2014). Deletion: The curse of the red-black tree. Journal of Functional Programming, 24(4), 423-433. https://doi.org/10.1017/S0956796814000227