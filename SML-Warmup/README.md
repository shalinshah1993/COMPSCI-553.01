##SML Warmup
This is a set of practice questions for SML NJ. The difficulty level increases with order. 

###Practice Excercise 1

- Write the `min` function which has `type int * int -> int` and returns the smaller of its two
arguments

- Write the `fib` function which has `type int -> int` and computes the nth Fibonacci number

- Write the `isPrime` function which has `type int -> bool` and determines whether or not its
argument is prime.

- Write the function `sumList` which has `type int list -> int` and computes the sum of all of
the items in the list.

- Write the function `squareList` which has `type int list -> int list` and returns a list of
the same length as its argument, where each item in the returned list is the square of the
corresponding item in the argument list. For example, `squareList [2,5,1,3]` should return
`[4,25,1,9]`

###Practice Excercise 2

- Using the following datatype declaration:

  ```
  datatype expr = NUM of int
                  | PLUS of expr * expr
                  | MINUS of expr * expr
                  | TIMES of expr * expr
                  | DIV of expr * expr
                  | F of expr list * (int list -> int)
  ```
  
  Write the function `eval: expr -> int` which evaluates an expression to a value. `NUM(x)`
  simply evaluates to `x`. `PLUS`, `MINUS`, `TIMES`, and `DIV` should recursively evaluate their
  sub-expressions, then perform the appropriate math operations. `F` exprs should recursively
  evaluate all the exprs in their `expr` list, then apply their function to the resulting integers.
  (Hint: You should use map in your `F` case.)

- Use fold to write the `flatten: ’a list list -> ’a list` function. The flatten function
  merges together a list of lists into a single list with all of the elements in their original
  order. For example: `flatten [[1,2,3], [4], [5,6], [], [7]]` should result in the list
  `[1,2,3,4,5,6,7]`.

- Use `fold` to implement your own version of `map`.
 
- Use `fold` to implement your own version of `filter`.
 
- Use `fold` to write the function `count: (’a -> bool) -> ’a list -> int` which returns a
  count of how many items in the list the `’a -> bool` function returned true for.

- Use `fold` to write `mapPartial: (’a -> ’b option) -> ’a list -> ’b list` this function
  is like a combination of map and filter. For each item of the input list, if the function applied
  to that item returns `SOME(b)`, then `b` appears in the output list. If `NONE` is returned, that
  item is dropped from the output list.

###Practice Excercise 3

- For this excercise, you will be filling in the contents of the following functor:

  ```
  functor F(M: ORD_MAP where type Key.ord_key = string)
  (S:ORD_SET where type Key.ord_key = string) :>
  sig
  val proc: string list -> S.set M.map
  end
  =
  struct
  ...
  end
  ```

  The proc function takes a list of strings (which are file names), and builds a map of sets. The
  map maps strings (i.e., words) to the set of files names in which they appear. Words are separated
  by spaces (or newlines). For example, if you were passed `["a.txt","b.txt"]` and `a.txt` had this
  contents:

  ```
  Hello World
  test
  ```

  and `b.txt` had this contents:

  ```
  a test
  input
  ```
  Your function should return a map that maps `"Hello”` and `“World”` to the set `{a.txt}`, `“test”` to the set `{a.txt, b.txt}` and `“test”` and `“input”` to the set `{b.txt}`. Checking out the `String`, and `TextIO` structures are highly recommended for implementing this function. You should then instantiate your functor on at least one structure instantiated from one of the built-in `ORD_MAP` and `ORD_SET` functors and test it out.
