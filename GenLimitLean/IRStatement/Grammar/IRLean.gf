-- Lean interpretation. The output is a closed proposition for #check_statement.
-- GLUE joins a family name to a field (O.language). Hypotheses are bound as
-- `∀ (_ : P), …` so that a later `by assumption` can supply a proof argument that the
-- English leaves implicit; by proof irrelevance the kernel does not distinguish proofs.
-- A label stands for its Lean constant; implicit arguments are left to elaboration.
concrete IRLean of IR = {
  lincat
    Doc, Outline, Concl, Items, Prop, Term, Ty, TyArgs, FamTy, Var, Fam, Lbl, Numeral, Ref, Pred = Str ;
    Names = {c, sp : Str} ;
    -- s: arguments of an application; c: the same, separated by commas, for a list literal.
    Args = {s, c : Str} ;
    Binds = Str ;
  oper
    par : Str -> Str = \s -> "(" ++ s ++ ")" ;
    field : Str -> Str -> Str = \o,f -> o ++ "GLUE" ++ f ;
    hyp : Str -> Str -> Str = \p,d -> "∀ ( _ :" ++ p ++ ") ," ++ d ;
    op : Str -> Str -> Str -> Str = \o,a,b -> par (a ++ o ++ b) ;
  lin
    Reading d = d ;

    LetTy x t d = "∀ (" ++ x ++ ":" ++ t ++ ") ," ++ d ;
    LetMany ns t d = "∀ (" ++ ns.sp ++ ":" ++ t ++ ") ," ++ d ;
    LetTyWith x t p d = "∀ (" ++ x ++ ":" ++ t ++ ") ," ++ hyp p d ;
    LetIn x a d = "∀" ++ x ++ "∈" ++ a ++ "," ++ d ;
    LetInWith x a p d = "∀" ++ x ++ "∈" ++ a ++ "," ++ hyp p d ;
    -- "Let t ≥ T" binds a natural number.
    LetGe x lo d = "∀ (" ++ x ++ ": ℕ ) ," ++ hyp (lo ++ "≤" ++ x) d ;
    AssumeDecEq a d = "∀ [ DecidableEq" ++ a ++ "] ," ++ d ;
    AssumeClass a l d = "∀ [" ++ l ++ a ++ "] ," ++ d ;
    LetFamily f t d = "∀ (" ++ f ++ ":" ++ t ++ ") ," ++ d ;
    DefineFam f v d = "let" ++ f ++ ":=" ++ v ++ ";" ++ d ;
    AssumeClassOver l ts d = "∀ [" ++ l ++ ts ++ "] ," ++ d ;
    Define x v d = "let" ++ x ++ ":=" ++ v ++ ";" ++ d ;
    DefineSeq o x v d = "let" ++ o ++ ":= fun" ++ x ++ "=>" ++ v ++ ";" ++ d ;
    DefinePred a t q d = "let" ++ a ++ ":= fun ( subject :" ++ t ++ ") =>" ++ q ++ ";" ++ d ;
    Suppose p d = hyp p d ;
    SupposeNamed h p d = "∀ (" ++ h ++ ":" ++ p ++ ") ," ++ d ;
    ThereIs x t ns d = "depends_only% [" ++ ns.c ++ "] ( ∃" ++ x ++ ":" ++ t ++ "," ++ d ++ ")" ;
    ThereIsFree x t d = "( ∃" ++ x ++ ":" ++ t ++ "," ++ d ++ ")" ;
    ThereAre bs ns d = "depends_only% [" ++ ns.c ++ "] (" ++ bs ++ d ++ ")" ;
    ThereAreFree bs d = "(" ++ bs ++ d ++ ")" ;
    OneBind x t = "∃" ++ x ++ ":" ++ t ++ "," ;
    MoreBinds x t bs = "∃" ++ x ++ ":" ++ t ++ "," ++ bs ;

    ThenInfinite a d = "∃ ( _ : Set.Infinite" ++ a ++ ") ," ++ d ;
    FactNamed h p d = "( ∃ (" ++ h ++ ":" ++ p ++ ") ," ++ d ++ ")" ;
    ListIncreasing u a d = "let" ++ u ++ ":= IRStatement.increasingEnumeration" ++ a ++ "( by assumption ) ;" ++ d ;
    Then c = c ;
    Claim p = p ;
    Finally p = p ;
    Also p c = par p ++ "∧" ++ par c ;
    AllHold xs = xs ;
    Equivalent a b = par a ++ "↔" ++ par b ;
    EitherOr a b = par a ++ "∨" ++ par b ;
    ExactlyOne p q = par (par p ++ "∧ ¬" ++ par q) ++ "∨" ++ par ("¬" ++ par p ++ "∧" ++ par q) ;
    ByDefinition p q = par p ++ "↔" ++ par q ;
    ByDefinitionThen p d = par p ++ "↔" ++ par d ;
    DefinedAs a b = par (a ++ "=" ++ b) ;
    DefinedType a b = par (a ++ "=" ++ b) ;
    OneItem o = o ;
    MoreItems o xs = par o ++ "∧" ++ par xs ;

    TNat = "ℕ" ;
    TReal = "ℝ" ;
    TInt = "ℤ" ;
    TBool = "Bool" ;
    TProp = "Prop" ;
    TType = "Type _" ;
    TType0 = "Type" ;
    TSort = "Sort _" ;
    TVar a = a ;
    TVarApp x xs = par (x ++ xs.s) ;
    TLblApp l k = par (l ++ k) ;
    TLblAppPlus l d k = par (l ++ par (d ++ "+" ++ k)) ;
    TMember a = par ("↥" ++ a) ;
    TFin k = par ("Fin" ++ k) ;
    TFinUpTo m = par ("Fin" ++ par (m ++ "+ 1")) ;
    TFamily f = f ;
    TLangFamily f = par (field f ".language") ;
    TSeq t = "( ℕ →" ++ t ++ ")" ;
    TFinset t = "( Finset" ++ t ++ ")" ;
    TSet t = "( Set" ++ t ++ ")" ;
    TList t = "( List" ++ t ++ ")" ;
    TOption t = "( Option" ++ t ++ ")" ;
    TEquiv a b = "(" ++ a ++ "≃" ++ b ++ ")" ;
    TFun a b = "(" ++ a ++ "→" ++ b ++ ")" ;
    TProd a b = "(" ++ a ++ "×" ++ b ++ ")" ;
    TSum a b = "(" ++ a ++ "⊕" ++ b ++ ")" ;
    TEmbed a b = "(" ++ a ++ "↪" ++ b ++ ")" ;
    TLbl l = l ;
    TLblOver l ts = par (l ++ ts) ;
    OneTy t = t ;
    MoreTy t ts = t ++ ts ;
    NatLanguages = "GenLimit.OracleFamily" ;
    LanguagesOver t = "( GenLimit.KM.Transport.IndexedOracleFamily" ++ t ++ ")" ;

    RVar x = x ;
    RFam f = f ;
    OneName r = {c = r ; sp = r} ;
    MoreNames r ns = {c = r ++ "," ++ ns.c ; sp = r ++ ns.sp} ;

    V x = x ;
    FamT f = f ;
    NumT n = n ;
    LblT l = l ;
    LblApp l xs = par (l ++ xs.s) ;
    Call f xs = par (f ++ xs.s) ;
    Lang f i = par (field f ".language" ++ i) ;
    LangFamily f = par (field f ".language") ;
    Diff = op "\\" ;
    Union = op "∪" ;
    Inter = op "∩" ;
    Add = op "+" ;
    Minus = op "-" ;
    Mul = op "*" ;
    Div = op "/" ;
    Pow = op "^" ;
    Neg a = par ("-" ++ a) ;
    Cast a = par ("↑" ++ a) ;
    Lam x b = par ("fun" ++ x ++ "=>" ++ b) ;
    LamTy x t b = par ("fun (" ++ x ++ ":" ++ t ++ ") =>" ++ b) ;
    LamP x p = par ("fun" ++ x ++ "=>" ++ p) ;
    FirstTerms n s t = par ("IRStatement.FirstTerms.firstTerms" ++ s ++ t) ;
    SetOfTy x t p = "{" ++ x ++ ":" ++ t ++ "|" ++ p ++ "}" ;
    SetOfOutside x t a p = "{" ++ x ++ ":" ++ t ++ "| (" ++ x ++ "∉" ++ a ++ ") ∧" ++ par p ++ "}" ;
    FilterSet i a p = par ("Finset.filter ( fun" ++ i ++ "=>" ++ p ++ ")" ++ a) ;
    KMGenerator f = par ("GenLimit.OracleFamily.kmGenerator" ++ f) ;
    PromptedGenerator f e = par ("GenLimit.KM.Prompted.generatorOfEquiv" ++ e ++ f) ;
    RunAt g s t = par (g ++ s ++ t) ;
    RunPromptedAt g s q t = par (g ++ s ++ q ++ "( by assumption )" ++ t) ;
    Pair a b = "(" ++ a ++ "," ++ b ++ ")" ;
    UnitT = "()" ;
    ListNil = "[]" ;
    ListOf xs = "[" ++ xs.c ++ "]" ;
    -- The membership proof is left to Lean; by proof irrelevance any proof gives the same term.
    Elem a = "( ⟨" ++ a ++ ", by first | assumption | exact ⟨ _ , rfl ⟩ | simp ⟩ )" ;
    FinsetSet a = par ("Finset.toSet" ++ a) ;
    OneArg a = {s = a ; c = a} ;
    MoreArgs a xs = {s = a ++ xs.s ; c = a ++ "," ++ xs.c} ;

    Mem = op "∈" ;
    NotMem = op "∉" ;
    Sub a b = par ("binrel% HasSubset.Subset" ++ a ++ b) ;
    NotSub a b = par ("¬" ++ par ("binrel% HasSubset.Subset" ++ a ++ b)) ;
    Eq = op "=" ;
    Ne = op "≠" ;
    Le = op "≤" ;
    Lt = op "<" ;
    Ge = op "≥" ;
    Gt = op ">" ;
    CardAtLeast s n = par (n ++ "≤ Finset.card" ++ s) ;
    LengthAtLeast c n = par (n ++ "≤ List.length" ++ c) ;
    IsPrefix p w = par ("List.IsPrefix" ++ p ++ w) ;
    ValuesExactly f a = par ("Set.range" ++ f ++ "=" ++ a) ;
    ValuesIn f a = par ("Set.range" ++ f ++ "⊆" ++ a) ;
    Injective f = par ("Function.Injective" ++ f) ;
    Confirms f x i = par (field f ".query" ++ i ++ x ++ "= true") ;
    Holds x a = par (a ++ x) ;
    IsLbl x l = par (l ++ x) ;
    IsNotLbl x l = par ("¬" ++ par (l ++ x)) ;
    LblHolds l xs = par (l ++ xs.s) ;
    LblFails l xs = par ("¬" ++ par (l ++ xs.s)) ;
    LblProp l = l ;
    VarHolds f xs = par (f ++ xs.s) ;
    VarFails f xs = par ("¬" ++ par (f ++ xs.s)) ;
    VarProp v = v ;
    And p q = par (p ++ "∧" ++ q) ;
    Or p q = par (p ++ "∨" ++ q) ;
    Iff p q = par (p ++ "↔" ++ q) ;
    Imp p q = par (p ++ "→" ++ q) ;
    Not p = par ("¬" ++ par p) ;
    ForallIn x a p = par ("∀" ++ x ++ "∈" ++ a ++ "," ++ p) ;
    ForallAtLeast x lo p = par ("∀ (" ++ x ++ ": ℕ ) ," ++ lo ++ "≤" ++ x ++ "→" ++ p) ;
    ForallOne x t p = par ("∀" ++ x ++ ":" ++ t ++ "," ++ p) ;
    ForallMany ns t p = par ("∀ (" ++ ns.sp ++ ":" ++ t ++ ") ," ++ p) ;
    ExistsSuch x t p = par ("∃" ++ x ++ ":" ++ t ++ "," ++ p) ;
    NoneSuch x t p = par ("¬" ++ par ("∃" ++ x ++ ":" ++ t ++ "," ++ p)) ;
    ExistsIn x a p = par ("∃" ++ x ++ "∈" ++ a ++ "," ++ p) ;
    ExistsGe x lo p = par ("∃ (" ++ x ++ ": ℕ ) ," ++ x ++ "≥" ++ lo ++ "∧" ++ p) ;
    ForallBelow x hi p = par ("∀ (" ++ x ++ ": ℕ ) ," ++ x ++ "<" ++ hi ++ "→" ++ p) ;
    ExistsBelow x hi p = par ("∃ (" ++ x ++ ": ℕ ) ," ++ x ++ "<" ++ hi ++ "∧" ++ p) ;
    Frequently x p = par ("∃ᶠ (" ++ x ++ ": ℕ ) in Filter.atTop ," ++ p) ;
    Eventually x p = par ("∀ᶠ (" ++ x ++ ": ℕ ) in Filter.atTop ," ++ p) ;

    LongExtensions f = "∀ ( i n : ℕ ) , ∃ c , n ≤ List.length c ∧ ( subject ++ c ) ∈" ++ field f ".language" ++ "i" ;
}
