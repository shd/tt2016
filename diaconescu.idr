data Or a b = Inl a | Inr b
data And a b = MkPair a b

Reflx: {A : Type} -> (R: A -> A -> Type) -> Type
Reflx {A} R = (x : A) -> R x x

Symm: {A : Type} -> (R: A -> A -> Type) -> Type
Symm {A} R = (x : A) -> (y : A) -> R x y -> R y x

Trans: {A : Type} -> (R: A -> A -> Type) -> Type
Trans {A} R = (x : A) -> (y : A) -> (z : A) -> R x y -> R y z -> R x z

data IsEquivalence: {A : Type} -> (R: A -> A -> Type) -> Type where
    EqProof: {A: Type} -> (R: A -> A -> Type) -> Reflx {A} R -> Symm {A} R -> Trans {A} R -> IsEquivalence {A} R

record Setoid where
    constructor MkSetoid
    Carrier: Type
    Equiv: Carrier -> Carrier -> Type
    EquivProof: IsEquivalence Equiv

refl_eq: {Carrier: Type} -> Reflx {A=Carrier} (=)
refl_eq x = Refl {x=x}

symm_eq: {Carrier: Type} -> Symm {A = Carrier} (=)
symm_eq x y = \(Refl {x=p}) => Refl {x=p}

trans_eq: {Carrier: Type} -> Trans {A = Carrier} (=)
trans_eq a b c = \(Refl{x=p}) => \(Refl{x=p}) => Refl {x=p}

e: {Carrier: Type} -> IsEquivalence {A=Carrier} (=)
e {Carrier} = EqProof {A=Carrier} (=) refl_eq symm_eq trans_eq

intensional_setoid: Type -> Setoid
intensional_setoid t = MkSetoid t (=) (e {Carrier=t})

data Map: (A:Setoid) -> (B:Setoid) -> Type where
  MkMap: {A:Setoid} -> {B:Setoid} -> (f: (Carrier A) -> (Carrier B)) -> 
     ({x:Carrier A} -> {y:Carrier A} -> 
     ((Equiv A) x y) -> ((Equiv B) (f x) (f y))) -> Map A B

MapF: {A:Setoid} -> {B:Setoid} -> Map A B -> (Carrier A -> Carrier B)
MapF (MkMap {A} {B} f ext) = f

MapExt: {A:Setoid} -> {B:Setoid} -> (p: Map A B) -> 
     ({x:Carrier A} -> {y:Carrier A} -> ((Equiv A) x y) -> ((Equiv B) (MapF p x) (MapF p y)))
MapExt (MkMap {A} {B} f ext) = ext

Rel: Type -> Type -> Type
Rel a b = a -> b -> Type

postulate ext_ac: {I: Setoid} -> {S: Setoid} -> 
  (A: Rel (Carrier I) (Carrier S)) -> 
  ((x: Carrier I) -> (g : Carrier S ** A x g)) ->
  (chs: (Map I S) ** ((w: Carrier I) -> A w ((MapF chs) w)))

excluded_middle: (P: Type) -> Or P (Not P)
excluded_middle P = decide
  where
    Discrete: Setoid
    Discrete = intensional_setoid Bool

    strange_eq: Bool -> Bool -> Type
    strange_eq x y = Or (x = y) P

    Strange: Setoid
    Strange = MkSetoid Bool strange_eq strange_eq_equivalence
      where
        postulate strange_eq_equivalence: IsEquivalence {A = Bool} strange_eq

    ff: (f: Map Strange Discrete ** ((x: Bool) -> strange_eq x ((MapF f) x)))
    ff = ext_ac {I = Strange} {S = Discrete} strange_eq (\x:Bool => (x ** Inl Refl))

    fx: Map Strange Discrete
    fx = getWitness ff

    decide: Or P (Not P)
    decide with (decEq ((MapF fx) True) ((MapF fx) False))
       | No pr = Inr (\px => pr (MapExt fx (Inr px)))
       | Yes pr = believe_me pr
