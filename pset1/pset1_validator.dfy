include "pset1.dfy"

module Pset1Validator {
  import Pset1

  method Tester() {
    var s, m := Pset1.MaxSum(1928, 1);
    assert s == 1929;
    assert m == 1928;
  }

  method TestMaxSum(x: int, y: int) {
    var s, m := Pset1.MaxSum(x, y);
    var xx, yy := Pset1.ReconstructFromMaxSum(s, m);
    assert (xx == x && yy == y) || (xx == y && yy == x);
  }

  method TestSeq(s : seq<int>)
    requires |s| > 0
  {
    // Let's run the equivalent of a standard test case, though we'll see it's a
    // bit more involved than you might expect.
    var a := Pset1.SeqMin([1, 2, 3]);
    assert 1 in [1, 2, 3];
    // The last line is meant to serve as a hint to the theorem-prover!
    assert a == 1;
    // Dafny can't figure out the unique answer without the previous hint.
    
    // Now let's run some "tests" over an arbitrary sequence,
    // which goes well beyond what literal testing can accomplish.
    var smin := Pset1.SeqMin(s);
    var smax := Pset1.SeqMax(s);
    assert smin <= smax;

    // More generic tests using another method
    var srev := Pset1.Reverse(s);
    assert smin in srev;
    assert smax in srev;
    var srevmin := Pset1.SeqMin(srev);
    var srevmax := Pset1.SeqMax(srev);
    assert srevmin == smin;
    assert srevmax == smax;

    // And one last method
    var m := Pset1.SeqToMap(s);
    assert smin in m.Values;
    assert smax in m.Values;
  }
}
