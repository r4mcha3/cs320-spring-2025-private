
type 'a tree =
  | Leaf
  | Node2 of 'a tree * 'a * 'a tree
  | Node3 of 'a tree * 'a * 'a tree * 'a * 'a tree
  | Node4 of {
      left_tree : 'a tree;
      val1 : 'a;
      left_mid_tree : 'a tree;
      val2 : 'a;
      right_mid_tree : 'a tree;
      val3 : 'a;
      right_tree : 'a tree;
    }

let _example = Node3 (Leaf, 2, Node2 (Leaf, 3, Leaf), 4, Leaf)
