def reachTable (gens : List Nat) (bound : Nat) : Array Bool :=
  (List.range (bound + 1)).foldl
    (fun acc n =>
      let ok :=
        if n == 0 then
          true
        else
          gens.any (fun g => g ≠ 0 && g ≤ n && acc[n - g]!)
      acc.push ok)
    #[]

def canMake (gens : List Nat) (n : Nat) : Bool :=
  (reachTable gens n)[n]!

def frobeniusUpTo (gens : List Nat) (bound : Nat) : Nat :=
  let reach := reachTable gens bound
  ((List.range (bound + 1)).filter (fun n => !(reach[n]!))).foldr Nat.max 0

/-- All pairs (x, y) drawn from gens, both orders included. -/
def allPairs (gens : List Nat) : List (Nat × Nat) :=
  gens.flatMap (fun x => gens.map (fun y => (x, y)))

/-- The classical two-generator Frobenius number x·y - x - y, valid when
x and y are coprime. Adding more generators to a semigroup can only
make more numbers representable, never fewer — so the true Frobenius
number of the full generator list is always ≤ this value, for ANY
coprime pair drawn from it. That's what makes it a rigorous,
formula-independent upper bound rather than a guessed one. -/
def twoGenBound (x y : Nat) : Nat := x * y - x - y

/-- Distinct prime factors of `n` (n ≥ 2), via simple trial division —
written as our own helper rather than depending on a specific Mathlib
factorization name. Takes explicit fuel so the recursion is structural
and kernel-unfoldable (no `partial` — `decide` works on this again).
Fuel decreases every call regardless of branch, so fuel = n + 1 is
always enough: trial division only ever needs ~√n + (# prime factors)
steps, well under n. -/
def distinctPrimeFactorsAux (fuel n d : Nat) (acc : List Nat) : List Nat :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
    if n ≤ 1 then
      acc
    else if d * d > n then
      acc ++ [n]
    else if n % d == 0 then
      distinctPrimeFactorsAux fuel (n / d) d (if d ∈ acc then acc else acc ++ [d])
    else
      distinctPrimeFactorsAux fuel n (d + 1) acc

def distinctPrimeFactors (n : Nat) : List Nat :=
  distinctPrimeFactorsAux (n + 1) n 2 []

/-- Some generator not divisible by `p` — guaranteed to exist whenever
`gcd(gens) = 1`, since if `p` divided every generator it would divide
their gcd too. -/
def witnessNotDivisibleBy (gens : List Nat) (p : Nat) : Nat :=
  (gens.find? (fun m => m % p != 0)).getD 1

/-- Exercise 4.12's construction: given `a` (the first generator) with
distinct prime factors `p₁,...,pₙ`, build `b = a + a₁ + ⋯ + aₙ` so that
no `pₖ` divides `b` — making `a` and `b` coprime even when no two
*original* generators are. `b` is a genuine nonnegative combination of
generators, so it's a real element of the semigroup, and the "extra
generators can only shrink the gap set" argument applies to `(a, b)`
just as it would to two original generators. No longer `partial`: its
own recursion (structural on the prime list) was always fine — it only
had to be `partial` because it called the previously-`partial`
`distinctPrimeFactors`. -/
def constructCoprimePartner (gens : List Nat) (a : Nat) : Nat :=
  let primes := distinctPrimeFactors a
  let rec go (ps : List Nat) (primeProd partialSum : Nat) : Nat :=
    match ps with
    | [] => partialSum
    | p :: rest =>
      if partialSum % p == 0 then
        let m := witnessNotDivisibleBy gens p
        go rest (primeProd * p) (partialSum + primeProd * m)
      else
        go rest (primeProd * p) partialSum
  go primes 1 a

/-- Fallback bound for when no two original generators are coprime:
construct a guaranteed-coprime pair via `constructCoprimePartner`, then
apply the same classical two-generator formula. -/
def fallbackRigorousBound (gens : List Nat) : Nat :=
  match gens with
  | [] => 0
  | a :: _ => twoGenBound a (constructCoprimePartner gens a)

/-- Full rigorous bound: try the cheap direct pairwise-coprime search
first; only fall back to the Exercise 4.12 construction when that
search finds nothing. -/
def rigorousBoundFull (gens : List Nat) : Nat :=
  let candidates :=
    (allPairs gens).filterMap (fun (x, y) =>
      if x ≠ y && Nat.gcd x y == 1 then
        some (twoGenBound x y)
      else
        none)
  match candidates with
  | [] => fallbackRigorousBound gens
  | c :: cs => cs.foldl min c

/-- Frobenius number of `gens`, always rigorously bounded — falling back
to the constructive proof only when needed. -/
def OLDfrobeniusNumber (gens : List Nat) : Nat :=
  frobeniusUpTo gens (rigorousBoundFull gens)

/-- One residue's turn: if we've already found some way to reach it,
try extending by each generator and see if that beats the current best
route to the resulting residue. -/
def relaxResidue (gens : List Nat) (m : Nat) (dist : Array (Option Nat)) (r : Nat) :
    Array (Option Nat) :=
  match dist[r]! with
  | none => dist
  | some d =>
    gens.foldl
      (fun acc g =>
        let r' := (r + g) % m
        let cand := d + g
        match acc[r']! with
        | none => acc.set! r' (some cand)
        | some cur => if cand < cur then acc.set! r' (some cand) else acc)
      dist

/-- One full round: relax every residue once, in order. -/
def relaxRound (gens : List Nat) (m : Nat) (dist : Array (Option Nat)) :
    Array (Option Nat) :=
  (List.range m).foldl (relaxResidue gens m) dist

/-- The Apéry set of the smallest generator: for each residue r mod m,
the smallest semigroup element congruent to r. Computed by repeated
relaxation — since every generator is a strictly positive step, the
true shortest route to any residue never needs to revisit the same
residue twice (that would only add cost for no benefit), so it uses at
most m-1 steps. Hence m-1 full rounds of relaxation are always enough
to reach the final, correct answer. -/
def aperySet (gens : List Nat) (m : Nat) : Array (Option Nat) :=
  let init : Array (Option Nat) := (Array.replicate m none).set! 0 (some 0)
  (List.range (m - 1)).foldl (fun acc _ => relaxRound gens m acc) init

/-- Frobenius number via the Apéry set. Same underlying idea as
frobeniusUpTo, but bounded by the smallest generator instead of by the
Frobenius number itself — so it stays fast even when F is astronomical. -/
def frobeniusNumber (gens : List Nat) : Nat :=
  let m := gens.foldl Nat.min gens.head!
  let dist := aperySet gens m
  let reps := (List.range m).drop 1 |>.map (fun r => (dist[r]!).getD 0)
  reps.foldr Nat.max 0 - m

/-- Genus via the same Apéry set: g(S) = (1/m)(sum of the Apéry set) -
(m-1)/2, written over a common denominator so Nat's truncating
division doesn't corrupt the result along the way. -/
def genusApery (gens : List Nat) : Nat :=
  let m := gens.foldl Nat.min gens.head!
  let dist := aperySet gens m
  let total := (List.range m).foldl (fun acc r => acc + (dist[r]!).getD 0) 0
  (2 * total - m * (m - 1)) / (2 * m)

/-- The gaps: positive numbers up to `bound` that are NOT in the semigroup.
Builds the reachability table ONCE and reads it out, rather than calling
`canMake` per number — `canMake gens n` rebuilds the whole table from
scratch each time, which would make this quadratic in `bound`. -/
def gapsUpTo (gens : List Nat) (bound : Nat) : List Nat :=
  let reach := reachTable gens bound
  (List.range (bound + 1)).filter (fun n => n ≠ 0 && !(reach[n]!))

/-- The genus: how many gaps there are, searching up to `bound`.
NOTE: `genusApery` already computes this with no bound at all. Keep this
only as a cross-check on that function (see the example below). -/
def genusUpTo (gens : List Nat) (bound : Nat) : Nat :=
  (gapsUpTo gens bound).length

/-- The conductor, searched up to `bound`: smallest `c` with every `n ≥ c`
representable. Equals the Frobenius number + 1. -/
def conductorUpTo (gens : List Nat) (bound : Nat) : Nat :=
  frobeniusUpTo gens bound + 1

/-- The conductor, bound-free — uses the Apéry-based `frobeniusNumber`, so
no search window has to be chosen. Prefer this one. -/
def conductor (gens : List Nat) : Nat :=
  frobeniusNumber gens + 1

/-- The multiplicity: the smallest generator. Assumes `gens` is nonempty
and all generators are positive. -/
def multiplicity (gens : List Nat) : Nat :=
  gens.foldl Nat.min gens.head!
