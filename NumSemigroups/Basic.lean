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
def frobeniusNumber (gens : List Nat) : Nat :=
  frobeniusUpTo gens (rigorousBoundFull gens)
