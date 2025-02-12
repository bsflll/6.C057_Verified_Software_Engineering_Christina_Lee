// Your goal is to complete this file to a point where the three 'dafny'
// commands shown in the assignment write-up succeed!
// That means not only implementing the missing method but also adding
// annotations on the methods, sufficient for the "test cases" in
// pset1_validator.dfy all to pass (again, this can be checked with the three
// commands from the assignment write-up).

// Note that many methods admit different specifications at different levels of
// precision.  You will get full credit for any specification that gives enough
// detail for all of the "tests" to pass in pset1_validator.dfy!

// A _module_ is a unit of related definitions in Dafny.
// We use one to organize your solutions.
module Pset1 {
  // This method obviously returns the maximum and sum of two ingtegers,
  // right?  Your first task is to add 'ensures' annotations on the method
  // to record what correctness means for this method.

  // Given two integers x and y, MaxSum returns their sum and their maximum.
  method MaxSum(x: int, y: int) returns (s: int, m: int)
  {
    s := x + y;
    if x < y {
      m := y;
    } else {
      m := x;
    }
  }

  // Now implement this related method (the only place on this assignment
  // where we ask you to write executable code, rather than proof-related
  // annnotations).  Also give it a proper specification, indicating that it can
  // reconstruct two integers, given their sum ('s') and maximum ('m').
  // HINT: this one probably deserves a 'requires' clause, because it will not
  // be able to find correct answers for some inputs.
  method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
  {
    // ...your code here...
  }

  // Add a sufficient specification for this method.
  method SeqMin(s: seq<int>) returns (m: int)
  {
    assert forall v :: v in s ==> v == s[0] || v in s[1..];
    // This assertion is a hint to Dafny, which should make it easier for Dafny
    // to prove your specification!
    // Once you get past parsing the math notation, the assertion says something
    // pretty obvious: every element of the sequence 's' is either the first
    // element or belongs to the tail of the sequence (everything _after_ the
    // first element).  However, Dafny doesn't make use of this fact without
    // prompting.
    
    if |s| == 1 {
      m := s[0];
    } else {
      var m' := SeqMin(s[1..]);
      if m' < s[0] {
        m := m';
      } else {
        m := s[0];
      }
    }
  }

  // Also add a specification for this twin of 'SeqMin'.
  method SeqMax(s: seq<int>) returns (m: int)
  {
    assert forall v :: v in s ==> v == s[0] || v in s[1..];
    
    if |s| == 1 {
      m := s[0];
    } else {
      var m' := SeqMax(s[1..]);
      if m' > s[0] {
        m := m';
      } else {
        m := s[0];
      }
    }
  }

  // Likewise for this method, which reverses a sequence (returning a new
  // one).
  // HINT: here you can get away with a specification significantly less precise
  // than one that literally says "yes, returns a new sequence that is the
  // reversal of the argument."
  method Reverse(s: seq<int>) returns (r: seq<int>)
  {
    if |s| == 0 {
      r := [];
    } else {
      var r' := Reverse(s[1..]);
      r := r' + [s[0]];
    }
  }

  // Maybe the hardest part!
  // But it's "just" another case of writing a good specification for this method.
  // The English version is that the method converts a sequence (immutable array)
  // into a finite map, keyed off of integer indices within the original.
  method SeqToMap(s: seq<int>) returns (m: map<int, int>)
  {
    if |s| == 0 {
      m := map[];
    } else {
      var m' := SeqToMap(s[..|s|-1]);
      m := m'[|s|-1 := s[|s|-1]];
    }
  }
}
