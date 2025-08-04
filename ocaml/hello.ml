let () = print_endline "Hello, World!"

module IntSet = Set.Make(struct
  type t = int
  let compare = compare
end)

let numbers = IntSet.singleton 1