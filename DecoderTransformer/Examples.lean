import DecoderTransformer

namespace DecoderTransformer

/-!
# Small executable sanity checks

These examples instantiate the abstract aggregator with natural numbers.  The
refinement theorem itself remains fully polymorphic; these checks only make
the list order and cache contents visible during local development.
-/

def toyAggregator (q : Nat) (ks vs : List Nat) : Nat :=
  q + ks.length + vs.length

example :
    cachedAttention (fun x : Nat => x) (fun x => x + 10) (fun x => x + 20)
      toyAggregator [1, 2, 3] =
      causalAttention (fun x : Nat => x) (fun x => x + 10) (fun x => x + 20)
        toyAggregator [1, 2, 3] := by
  exact cachedAttention_eq_causalAttention _ _ _ _ _

example :
    (cachedRun (fun x : Nat => x) (fun x => x + 10) (fun x => x + 20)
      toyAggregator emptyCache [1, 2, 3]).1 =
      cacheOf (fun x : Nat => x + 10) (fun x => x + 20) [1, 2, 3] := by
  exact finalCache_eq_fullProjections _ _ _ _ _

end DecoderTransformer
