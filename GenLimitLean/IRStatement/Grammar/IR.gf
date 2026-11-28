-- Abstract syntax of the IR statement reader. Every construction has an English
-- rendering (IREng) and a Lean interpretation (IRLean) with the same slots.
-- A paper's lexicon adds only names: variables (Var), oracle families (Fam), numerals
-- (Numeral) and labels of Lean constants (Lbl). A label is made from the constant's Lean
-- name by one fixed algorithm, so it needs no review of its own.
abstract IR = {
  flags startcat = Doc ;
  cat Doc ; Outline ; Concl ; Items ; Prop ; Term ; Args ; Ty ; TyArgs ; FamTy ;
      Var ; Fam ; Lbl ; Numeral ; Ref ; Names ; Pred ; Binds ;
  fun
    Reading : Outline -> Doc ;

    -- Introductions, assumptions and choices.
    LetTy : Var -> Ty -> Outline -> Outline ;
    LetMany : Names -> Ty -> Outline -> Outline ;
    LetTyWith : Var -> Ty -> Prop -> Outline -> Outline ;
    LetIn : Var -> Term -> Outline -> Outline ;
    LetInWith : Var -> Term -> Prop -> Outline -> Outline ;
    LetGe : Var -> Term -> Outline -> Outline ;
    AssumeDecEq : Var -> Outline -> Outline ;
    AssumeClass : Var -> Lbl -> Outline -> Outline ;
    LetFamily : Fam -> FamTy -> Outline -> Outline ;
    DefineFam : Fam -> Term -> Outline -> Outline ;
    AssumeClassOver : Lbl -> TyArgs -> Outline -> Outline ;
    Define : Var -> Term -> Outline -> Outline ;
    DefineSeq : Var -> Var -> Term -> Outline -> Outline ;
    DefinePred : Var -> Ty -> Pred -> Outline -> Outline ;
    Suppose : Prop -> Outline -> Outline ;
    SupposeNamed : Var -> Prop -> Outline -> Outline ;
    ThereIs : Var -> Ty -> Names -> Outline -> Outline ;
    ThereIsFree : Var -> Ty -> Outline -> Outline ;
    ThereAre : Binds -> Names -> Outline -> Outline ;
    ThereAreFree : Binds -> Outline -> Outline ;
    OneBind : Var -> Ty -> Binds ;
    MoreBinds : Var -> Ty -> Binds -> Binds ;

    -- Conclusions.
    ThenInfinite : Var -> Outline -> Outline ;
    FactNamed : Var -> Prop -> Outline -> Outline ;
    ListIncreasing : Var -> Var -> Outline -> Outline ;
    Then : Concl -> Outline ;
    Claim : Prop -> Outline ;
    Finally : Prop -> Concl ;
    Also : Prop -> Concl -> Concl ;
    AllHold : Items -> Outline ;
    Equivalent, EitherOr : Outline -> Outline -> Outline ;

    -- Definition statements of the glossary.
    ByDefinition : Prop -> Prop -> Outline ;
    ByDefinitionThen : Prop -> Outline -> Outline ;
    DefinedAs : Term -> Term -> Outline ;
    DefinedType : Ty -> Ty -> Outline ;
    ExactlyOne : Prop -> Prop -> Outline ;
    OneItem : Outline -> Items ;
    MoreItems : Outline -> Items -> Items ;

    -- Types of bound variables.
    TNat, TReal, TInt, TBool, TProp, TType, TType0, TSort : Ty ;
    TSeq, TFinset, TSet, TList, TOption : Ty -> Ty ;
    TVar : Var -> Ty ;
    TVarApp : Var -> Args -> Ty ;
    TLblApp : Lbl -> Numeral -> Ty ;
    TLblAppPlus : Lbl -> Var -> Numeral -> Ty ;
    TMember : Term -> Ty ;
    TFin : Term -> Ty ;
    TFinUpTo : Numeral -> Ty ;
    TFamily, TLangFamily : Fam -> Ty ;
    TEquiv, TFun, TProd, TSum, TEmbed : Ty -> Ty -> Ty ;
    TLbl : Lbl -> Ty ;
    TLblOver : Lbl -> TyArgs -> Ty ;
    OneTy : Ty -> TyArgs ;
    MoreTy : Ty -> TyArgs -> TyArgs ;
    NatLanguages : FamTy ;
    LanguagesOver : Ty -> FamTy ;

    -- Lists of names.
    RVar : Var -> Ref ;
    RFam : Fam -> Ref ;
    OneName : Ref -> Names ;
    MoreNames : Ref -> Names -> Names ;

    -- Terms.
    V : Var -> Term ;
    FamT : Fam -> Term ;
    NumT : Numeral -> Term ;
    LblT : Lbl -> Term ;
    LblApp : Lbl -> Args -> Term ;
    Call : Var -> Args -> Term ;
    Lang : Fam -> Var -> Term ;
    LangFamily : Fam -> Term ;
    Diff, Union, Inter, Add, Minus, Mul, Div, Pow : Term -> Term -> Term ;
    Neg, Cast : Term -> Term ;
    Lam : Var -> Term -> Term ;
    LamTy : Var -> Ty -> Term -> Term ;
    LamP : Var -> Prop -> Term ;
    FirstTerms : Var -> Var -> Var -> Term ;
    SetOfTy : Var -> Ty -> Prop -> Term ;
    SetOfOutside : Var -> Ty -> Term -> Prop -> Term ;
    FilterSet : Var -> Term -> Prop -> Term ;
    KMGenerator : Fam -> Term ;
    PromptedGenerator : Fam -> Var -> Term ;
    RunAt : Var -> Var -> Var -> Term ;
    RunPromptedAt : Var -> Var -> Var -> Var -> Term ;
    Pair : Term -> Term -> Term ;
    UnitT, ListNil : Term ;
    ListOf : Args -> Term ;
    Elem : Term -> Term ;
    FinsetSet : Term -> Term ;
    OneArg : Term -> Args ;
    MoreArgs : Term -> Args -> Args ;

    -- Propositions.
    Mem, NotMem, Sub, NotSub, CardAtLeast, LengthAtLeast, IsPrefix : Term -> Term -> Prop ;
    Eq, Ne, Le, Lt, Ge, Gt : Term -> Term -> Prop ;
    ValuesExactly, ValuesIn : Var -> Term -> Prop ;
    Injective : Var -> Prop ;
    Confirms : Fam -> Term -> Var -> Prop ;
    Holds : Term -> Var -> Prop ;
    IsLbl, IsNotLbl : Term -> Lbl -> Prop ;
    LblHolds, LblFails : Lbl -> Args -> Prop ;
    LblProp : Lbl -> Prop ;
    VarHolds, VarFails : Var -> Args -> Prop ;
    VarProp : Var -> Prop ;
    And, Or, Iff, Imp : Prop -> Prop -> Prop ;
    Not : Prop -> Prop ;
    ForallIn : Var -> Term -> Prop -> Prop ;
    ForallAtLeast : Var -> Term -> Prop -> Prop ;
    ForallOne : Var -> Ty -> Prop -> Prop ;
    ForallMany : Names -> Ty -> Prop -> Prop ;
    ExistsSuch, NoneSuch : Var -> Ty -> Prop -> Prop ;
    ExistsIn, ExistsGe : Var -> Term -> Prop -> Prop ;
    ForallBelow, ExistsBelow : Var -> Term -> Prop -> Prop ;
    Frequently, Eventually : Var -> Prop -> Prop ;

    -- Properties of one object, used to define a local adjective.
    LongExtensions : Fam -> Pred ;
}
