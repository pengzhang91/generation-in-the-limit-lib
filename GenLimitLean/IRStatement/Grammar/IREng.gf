-- English rendering. GLUE marks a place where the display has no space (as in o(t),
-- L_z, "number,"), PARA a paragraph break, and INMARK/NEXTMARK/OUTMARK a bullet list.
-- The Markdown tokenizer in reader.py restores all of them from the visible text, so
-- spacing, paragraphs and lists are parsed.
concrete IREng of IR = {
  param
    SKind = KLet | KSup | KThere | KThen | KList ;
    -- Denied: a claim that ends in "does not hold", or a negated frame ("X is not *label* for Y"); it joins "and"/"or" like an atom but takes
    -- no trailing quantifier, since "P does not hold for every x" could deny the quantifier.
    PKind = Atom | Denied | Conj | Disj | Cond | Quant | Post ;
    Count = One | Many ;
    -- Simple: names, applications, L_i, {…}; Infix: a ∖ b, a + b; Described: noun phrases.
    TPrec = Simple | Infix | Described ;
    -- A type with a symbol (ℕ, α) is bound as "x ∈ ℕ" or "S ⊆ α"; other types in words.
    Sym = HasSym | NoSym ;
    -- A label that begins with a verb (has, is, can, …) takes no copula: "H has …", not "H is has …".
    Verbal = Copular | Verb ;
    -- What a type constructor needs to know about its argument to choose its wording.
    TyKind = KNat | KVar | KFun | KOther ;
  lincat
    Doc, Var, Ref, FamTy, Pred, Concl, Numeral, Args, Items = Str ;
    Lbl = {s, pl, art : Str ; v : Verbal} ;
    Binds = {s : Str ; n : Count} ;
    Term = {s : Str ; p : TPrec} ;
    -- inl: the same sentences on one line (inside a bullet); afterSup: the form right after
    -- an assumption ("Then there is …"); items: the bullets alone, for a list that follows a choice
    -- ("… with the following properties:").
    Outline = {s, inl, afterSup, afterSupInl, items : Str ; k : SKind} ;
    -- c: the form that starts a sentence.
    Prop = {s, c : Str ; k : PKind} ;
    -- ref: the type as the domain or codomain of a function ("lists of natural numbers", "ℕ").
    Ty = {sg, pl, compl, sym, bind, art, ref : Str ; has : Sym ; kind : TyKind} ;
    TyArgs = {s, c : Str ; n : Count} ;
    Fam = {s, lang : Str} ;
    Names = {s : Str ; n : Count} ;
  oper
    glue : Str -> Str -> Str = \a,b -> a ++ "GLUE" ++ b ;
    stop : Str = "GLUE" ++ "." ;
    comma : Str = "GLUE" ++ "," ;
    colon : Str = "GLUE" ++ ":" ;
    sub : Str -> Str -> Str = \l,i -> l ++ "GLUE" ++ "_" ++ "GLUE" ++ i ;
    paren : Str -> Str = \s -> "(" ++ "GLUE" ++ s ++ "GLUE" ++ ")" ;
    braces : Str -> Str = \s -> "{" ++ "GLUE" ++ s ++ "GLUE" ++ "}" ;
    bullets : Str -> Str = \s -> colon ++ "INMARK" ++ s ++ "OUTMARK" ;
    -- Introductions share a paragraph, and so do the sentences of a conclusion.
    -- Each assumption and each choice is a paragraph of its own.
    continue : SKind -> {s, inl, afterSup, afterSupInl, items : Str ; k : SKind} -> Str = \cur,d ->
      case <cur, d.k> of { <KLet, KLet> => d.s ; <KThen, KThen> => d.s ; <KThere, KThen> => d.s ;
                           <KThen, KList> => d.s ; <KThere, KList> => d.s ;
                           _ => "PARA" ++ d.s } ;
    sentence : SKind -> Str -> {s, inl, afterSup, afterSupInl, items : Str ; k : SKind} ->
               {s, inl, afterSup, afterSupInl, items : Str ; k : SKind} = \k,s,d ->
      let t : Str = s ++ stop in
      {s = t ++ continue k d ; inl = t ++ d.inl ; afterSup = t ++ continue k d ; afterSupInl = t ++ d.inl ;
       items = [] ; k = k} ;
    final : Str -> {s, inl, afterSup, afterSupInl, items : Str ; k : SKind} = \s ->
      {s = s ; inl = s ; afterSup = s ; afterSupInl = s ; items = [] ; k = KThen} ;
    -- A choice: "There is x ∈ T with the following property." and the rest of the text; when the
    -- rest is a list, "There is x ∈ T with the following properties:" and the bullets.
    choice : Str -> Str -> Str -> {s, inl, afterSup, afterSupInl, items : Str ; k : SKind} ->
             {s, inl, afterSup, afterSupInl, items : Str ; k : SKind} = \there,thenThere,head,d ->
      case d.k of {
        KList => let c : Str = head ++ "with the following properties" ++ d.items in
          {s = there ++ c ; inl = there ++ c ; afterSup = thenThere ++ c ; afterSupInl = thenThere ++ c ;
           items = [] ; k = KThere} ;
        _ => let c : Str = head ++ "with the following property" ++ stop in
          {s = there ++ c ++ continue KThere d ; inl = there ++ c ++ d.inl ;
           afterSup = thenThere ++ c ++ continue KThere d ; afterSupInl = thenThere ++ c ++ d.inl ;
           items = [] ; k = KThere} } ;
    atom : Str -> {s, c : Str ; k : PKind} = \s -> {s = s ; c = s ; k = Atom} ;
    fails : Str -> {s, c : Str ; k : PKind} = \s -> {s = s ++ "does not hold" ; c = s ++ "does not hold" ; k = Denied} ;
    -- A negated sentence frame ("X is not *label* for Y"), made in the lexicon: also no quantifier after it.
    denied : Str -> {s, c : Str ; k : PKind} = \s -> {s = s ; c = s ; k = Denied} ;
    -- A claim that begins with an English word has a capitalized form.
    worded : Str -> Str -> Str -> PKind -> {s, c : Str ; k : PKind} = \lower,upper,rest,k ->
      {s = lower ++ rest ; c = upper ++ rest ; k = k} ;
    -- A compound left operand is bracketed; a right operand is bracketed when it is a
    -- different connective, so "and" and "or" never hide a scope.
    left : {s, c : Str ; k : PKind} -> Str = \p -> case p.k of { Atom | Denied => p.s ; _ => paren p.s } ;
    leftC : {s, c : Str ; k : PKind} -> Str = \p -> case p.k of { Atom | Denied => p.c ; _ => paren p.s } ;
    rightOf : PKind -> {s, c : Str ; k : PKind} -> Str = \op,q -> case <op, q.k> of {
        <Conj, Disj> => paren q.s ; <Conj, Cond> => paren q.s ;
        <Disj, Conj> => paren q.s ; <Disj, Cond> => paren q.s ;
        <Cond, Atom> => q.s ; <Cond, _> => paren q.s ;
        _ => q.s } ;
    simple : Str -> {s : Str ; p : TPrec} = \s -> {s = s ; p = Simple} ;
    described : Str -> {s : Str ; p : TPrec} = \s -> {s = s ; p = Described} ;
    infix : Str -> {s : Str ; p : TPrec} -> {s : Str ; p : TPrec} -> {s : Str ; p : TPrec} = \op,a,b ->
      {s = tight a ++ op ++ tight b ; p = Infix} ;
    -- Operands of a relation bracket a noun phrase; operands of an operator bracket anything compound.
    operand : {s : Str ; p : TPrec} -> Str = \t -> case t.p of { Described => paren t.s ; _ => t.s } ;
    tight : {s : Str ; p : TPrec} -> Str = \t -> case t.p of { Simple => t.s ; _ => paren t.s } ;
    relation : Str -> {s : Str ; p : TPrec} -> {s : Str ; p : TPrec} -> {s, c : Str ; k : PKind} = \op,a,b ->
      atom (operand a ++ op ++ operand b) ;
    -- "Let x be <noun phrase>" but "Let x = <formula>".
    be : {s : Str ; p : TPrec} -> Str = \t -> case t.p of { Described => "be" ++ t.s ; _ => "=" ++ t.s } ;
    -- "Let z ∈ ℕ" or "Let x be a sequence of natural numbers".
    being : Str -> {sg, pl, compl, sym, bind, art : Str ; has : Sym ; kind : TyKind} -> Str = \x,t ->
      case t.has of { HasSym => x ++ t.bind ; NoSym => x ++ "be" ++ t.art ++ t.sg ++ t.compl } ;
    -- "T ∈ ℕ" or "a word c over A".
    some : Str -> {sg, pl, compl, sym, bind, art : Str ; has : Sym ; kind : TyKind} -> Str = \x,t ->
      case t.has of { HasSym => x ++ t.bind ; NoSym => t.art ++ t.sg ++ x ++ t.compl } ;
    -- "x ∈ ℕ" or "word x over A" after "every" or "no".
    bare : Str -> {sg, pl, compl, sym, bind, art : Str ; has : Sym ; kind : TyKind} -> Str = \x,t ->
      case t.has of { HasSym => x ++ t.bind ; NoSym => t.sg ++ x ++ t.compl } ;
    plural : {sg, pl, compl, sym, bind, art : Str ; has : Sym ; kind : TyKind} -> Str = \t ->
      case t.has of { HasSym => t.sym ; NoSym => t.pl ++ t.compl } ;
    worded_ty : Str -> Str -> Str -> Str -> Str -> {sg, pl, compl, sym, bind, art, ref : Str ; has : Sym ; kind : TyKind} =
      \sg,pl,compl,sym,art -> {sg = sg ; pl = pl ; compl = compl ; sym = sym ; bind = [] ; art = art ; ref = sym ;
                              has = NoSym ; kind = KOther} ;
    symbol_ty : Str -> Str -> Str -> Str -> {sg, pl, compl, sym, bind, art, ref : Str ; has : Sym ; kind : TyKind} =
      \sg,pl,sym,art -> {sg = sg ; pl = pl ; compl = [] ; sym = sym ; bind = "∈" ++ sym ; art = art ; ref = sym ;
                          has = HasSym ; kind = KOther} ;
    -- A collection type as a domain or codomain is named in words, unless its elements are
    -- functions: "a function from lists of natural numbers to ℕ", never two "from … to" in a row.
    collection : Str -> Str -> {sym, pl, compl : Str ; kind : TyKind} -> Str = \words,sym,t ->
      case t.kind of { KFun => sym ; _ => words } ;
    listed : Str -> {s : Str ; n : Count} -> Str = \x,xs ->
      case xs.n of { One => x ++ "and" ++ xs.s ; Many => x ++ comma ++ xs.s } ;
  lin
    Reading d = d.s ;

    LetTy x t d = sentence KLet ("Let" ++ being x t) d ;
    LetMany ns t d = sentence KLet ("Let" ++ ns.s ++ "be" ++ t.pl ++ t.compl) d ;
    LetTyWith x t p d = sentence KLet ("Let" ++ being x t ++ "with" ++ p.s) d ;
    LetIn x a d = sentence KLet ("Let" ++ x ++ "∈" ++ operand a) d ;
    LetInWith x a p d = sentence KLet ("Let" ++ x ++ "∈" ++ operand a ++ "with" ++ p.s) d ;
    LetGe x lo d = sentence KLet ("Let" ++ x ++ "≥" ++ operand lo) d ;
    AssumeDecEq a d = sentence KLet ("Assume that equality on" ++ a ++ "is decidable") d ;
    AssumeClass a l d = sentence KLet ("Assume that" ++ a ++ "is" ++ l.s) d ;
    LetFamily f t d = sentence KLet ("Let" ++ f.s ++ "be an indexed family of languages" ++
        sub f.lang "0" ++ comma ++ sub f.lang "1" ++ comma ++ sub f.lang "2" ++ comma ++ "…" ++ t ++ stop ++
        "Each" ++ sub f.lang "i" ++ "is infinite" ++ stop ++ f.s ++ "has a membership oracle") d ;
    Define x v d = sentence KLet ("Let" ++ x ++ be v) d ;
    -- A family given by a formula; its languages get their own letter.
    DefineFam f v d = sentence KLet ("Let" ++ f.s ++ be v ++ comma ++ "with languages" ++
        sub f.lang "0" ++ comma ++ sub f.lang "1" ++ comma ++ sub f.lang "2" ++ comma ++ "…") d ;
    AssumeClassOver l ts d = sentence KLet ("Assume that" ++ glue l.s (paren ts.c)) d ;
    DefineSeq o x v d = sentence KLet ("Let" ++ glue o (paren x) ++ be v) d ;
    DefinePred a t q d = sentence KLet ("Call" ++ t.art ++ t.sg ++ t.compl ++ a ++ "if it" ++ q) d ;
    -- Consecutive assumptions share a paragraph.
    Suppose p d = let s : Str = "Suppose that" ++ p.s ++ stop ;
                      next : Str = case d.k of { KSup => d.afterSup ; _ => "PARA" ++ d.afterSup } in
        {s = s ++ next ; inl = s ++ d.afterSupInl ; afterSup = s ++ next ; afterSupInl = s ++ d.afterSupInl ;
         items = [] ; k = KSup} ;
    SupposeNamed h p d = let s : Str = "Suppose that" ++ p.s ++ comma ++ "and call this assumption" ++ h ++ stop ;
                             next : Str = case d.k of { KSup => d.afterSup ; _ => "PARA" ++ d.afterSup } in
        {s = s ++ next ; inl = s ++ d.afterSupInl ; afterSup = s ++ next ; afterSupInl = s ++ d.afterSupInl ;
         items = [] ; k = KSup} ;
    ThereIs x t ns d = choice "There is" "Then there is" (some x t ++ comma ++ "depending only on" ++ ns.s ++ comma) d ;
    ThereIsFree x t d = choice "There is" "Then there is" (some x t) d ;
    ThereAre bs ns d = choice "There are" "Then there are" (bs.s ++ comma ++ "depending only on" ++ ns.s ++ comma) d ;
    ThereAreFree bs d = choice "There are" "Then there are" bs.s d ;
    OneBind x t = {s = some x t ; n = One} ;
    MoreBinds x t bs = {s = listed (some x t) bs ; n = Many} ;

    ThenInfinite a d = sentence KThen ("Then" ++ a ++ "is infinite") d ;
    FactNamed h p d = sentence KThen (p.c ++ "GLUE" ++ ";" ++ "call this fact" ++ h) d ;
    ListIncreasing u a d = sentence KThen ("Let" ++ u ++ "list the elements of" ++ a ++ "in increasing order") d ;
    Then c = final ("Then" ++ c) ;
    Claim p = final (p.c ++ stop) ;
    Finally p = p.s ++ stop ;
    Also p c = p.s ++ stop ++ "Also" ++ comma ++ c ;
    AllHold xs = let s : Str = "All of the following hold" ++ bullets xs in
      {s = s ; inl = s ; afterSup = s ; afterSupInl = s ; items = bullets xs ; k = KList} ;
    Equivalent a b = final ("The following are equivalent" ++ bullets (a.inl ++ "NEXTMARK" ++ b.inl)) ;
    EitherOr a b = final ("At least one of the following holds" ++ bullets (a.inl ++ "NEXTMARK" ++ b.inl)) ;
    ExactlyOne p q = final ("Exactly one of the following holds" ++ bullets (p.c ++ stop ++ "NEXTMARK" ++ q.c ++ stop)) ;
    ByDefinition p q = final ("By definition" ++ comma ++ left p ++ "if and only if" ++ rightOf Cond q ++ stop) ;
    ByDefinitionThen p d = let s : Str = "By definition" ++ comma ++ left p ++
                               "if and only if the following holds" ++ stop in
      {s = s ++ "PARA" ++ d.s ; inl = s ++ d.inl ; afterSup = s ++ "PARA" ++ d.s ; afterSupInl = s ++ d.inl ;
       items = [] ; k = KThen} ;
    DefinedAs a b = final ("By definition" ++ comma ++ operand a ++ "=" ++ operand b ++ stop) ;
    DefinedType a b = final ("By definition" ++ comma ++ a.art ++ a.sg ++ a.compl ++ "is" ++ b.art ++ b.sg ++ b.compl ++ stop) ;
    OneItem o = o.inl ;
    MoreItems o xs = o.inl ++ "NEXTMARK" ++ xs ;

    TNat = {sg = "natural number" ; pl = "natural numbers" ; compl = [] ; sym = "ℕ" ; bind = "∈" ++ "ℕ" ;
            art = "a" ; ref = "ℕ" ; has = HasSym ; kind = KNat} ;
    TReal = symbol_ty "real number" "real numbers" "ℝ" "a" ;
    TInt = symbol_ty "integer" "integers" "ℤ" "an" ;
    TBool = worded_ty "Boolean" "Booleans" [] "Bool" "a" ;
    TProp = worded_ty "proposition" "propositions" [] "Prop" "a" ;
    TType = worded_ty "type" "types" [] "Type" "a" ;
    TType0 = worded_ty "type" "types" ("in the lowest universe") (glue "Type" "₀") "a" ;
    TSort = worded_ty "sort" "sorts" [] "Sort" "a" ;
    -- An element of a type variable is described in words, so "x ∈ X" always means a set.
    TVar a = {sg = "element" ; pl = "elements" ; compl = "of" ++ a ; sym = a ; bind = [] ; art = "an" ; ref = a ;
              has = NoSym ; kind = KVar} ;
    -- The values of a function variable, such as L(i), as a type.
    TVarApp x xs = worded_ty "element" "elements" ("of" ++ glue x (paren xs)) (glue x (paren xs)) "an" ;
    -- A type constructor applied to a number, such as Lattice 1.
    TLblApp l k = worded_ty "element" "elements" ("of" ++ glue l.s (paren k)) (glue l.s (paren k)) "an" ;
    TLblAppPlus l d k = let sym : Str = glue l.s (paren (d ++ "+" ++ k)) in
      worded_ty "element" "elements" ("of" ++ sym) sym "an" ;
    -- The elements of a set S as a type (↥S). “member”, not “element”, so it never reads as TVar.
    TMember a = worded_ty "member" "members" ("of" ++ operand a) (glue "↥" (tight a)) "a" ;
    -- Fin k, the natural numbers below k; with a numeral, the largest one is shown.
    TFin k = let sym : Str = braces ("0" ++ comma ++ "…" ++ comma ++ tight k ++ "−" ++ "1") in
      symbol_ty ("element" ++ "of" ++ sym) ("elements" ++ "of" ++ sym) sym "an" ;
    TFinUpTo m = let sym : Str = braces ("0" ++ comma ++ "…" ++ comma ++ m) in
      symbol_ty ("element" ++ "of" ++ sym) ("elements" ++ "of" ++ sym) sym "an" ;
    -- An oracle family, or its family of languages, as the argument of a type constructor.
    TFamily f = worded_ty "element" "elements" ("of" ++ f.s) f.s "an" ;
    TLangFamily f = worded_ty "element" "elements" ("of" ++ paren (sub f.lang "i")) (paren (sub f.lang "i")) "an" ;
    -- A sequence is written in words; its symbol T^ℕ never coincides with a function type.
    TSeq t = worded_ty "sequence" "sequences" ("of" ++ t.pl ++ t.compl) (glue (glue t.sym "^") "ℕ") "a" ;
    -- A compound type symbol is always bracketed, so nested types read one way.
    TFinset t = let sym : Str = paren ("Finset" ++ t.sym) in
      worded_ty "finite set" "finite sets" ("of" ++ t.pl ++ t.compl) sym "a" **
        {ref = collection ("finite sets" ++ "of" ++ t.pl ++ t.compl) sym t} ;
    TSet t = let sym : Str = paren ("Set" ++ t.sym) in case t.kind of {
        KVar => {sg = "subset" ; pl = "subsets" ; compl = "of" ++ t.sym ; sym = sym ;
                 bind = "⊆" ++ t.sym ; art = "a" ; ref = "subsets" ++ "of" ++ t.sym ; has = HasSym ; kind = KOther} ;
        KNat => {sg = "subset" ; pl = "subsets" ; compl = "of" ++ t.sym ; sym = sym ;
                 bind = "⊆" ++ t.sym ; art = "a" ; ref = "subsets" ++ "of" ++ t.sym ; has = HasSym ; kind = KOther} ;
        _ => worded_ty "set" "sets" ("of" ++ t.pl ++ t.compl) sym "a" **
               {ref = collection ("sets" ++ "of" ++ t.pl ++ t.compl) sym t} } ;
    TList t = let sym : Str = paren ("List" ++ t.sym) in case t.kind of {
        KVar => worded_ty "word" "words" ("over" ++ t.sym) sym "a" ** {ref = "words" ++ "over" ++ t.sym} ;
        _ => worded_ty "list" "lists" ("of" ++ t.pl ++ t.compl) sym "a" **
               {ref = collection ("lists" ++ "of" ++ t.pl ++ t.compl) sym t} } ;
    TOption t = worded_ty "optional element" "optional elements" ("of" ++ t.sym) (paren ("Option" ++ t.sym)) "an" ;
    TEquiv a b = worded_ty "bijection" "bijections" ("from" ++ a.pl ++ a.compl ++ "to" ++ plural b)
                   (paren (a.sym ++ "≃" ++ b.sym)) "a" ;
    TFun a b = worded_ty "function" "functions" ("from" ++ a.ref ++ "to" ++ b.ref) (paren (a.sym ++ "→" ++ b.sym)) "a" **
                 {kind = KFun} ;
    TProd a b = worded_ty "pair" "pairs" ("in" ++ a.sym ++ "×" ++ b.sym) (paren (a.sym ++ "×" ++ b.sym)) "a" **
                  {ref = a.sym ++ "×" ++ b.sym} ;
    TSum a b = worded_ty "element" "elements" ("of" ++ a.sym ++ "⊕" ++ b.sym) (paren (a.sym ++ "⊕" ++ b.sym)) "an" ;
    TEmbed a b = worded_ty "embedding" "embeddings" ("of" ++ a.sym ++ "into" ++ b.sym) (paren (a.sym ++ "↪" ++ b.sym)) "an" ;
    TLbl l = worded_ty l.s l.pl [] l.s l.art ;
    TLblOver l ts = worded_ty l.s l.pl ("over" ++ ts.s) (glue l.s (paren ts.c)) l.art ;
    OneTy t = {s = t.sym ; c = t.sym ; n = One} ;
    MoreTy t ts = {s = listed t.sym ts ; c = t.sym ++ comma ++ ts.c ; n = Many} ;
    NatLanguages = "⊆" ++ "ℕ" ;
    LanguagesOver t = "of" ++ plural t ;

    RVar x = x ;
    RFam f = f.s ;
    OneName r = {s = r ; n = One} ;
    MoreNames r ns = {s = listed r ns ; n = Many} ;

    V x = simple x ;
    FamT f = simple f.s ;
    NumT n = simple n ;
    LblT l = simple l.s ;
    LblApp l xs = simple (glue l.s (paren xs)) ;
    Call f xs = simple (glue f (paren xs)) ;
    Lang f i = simple (sub f.lang i) ;
    LangFamily f = simple (paren (sub f.lang "i")) ;
    Diff = infix "∖" ;
    Union = infix "∪" ;
    Inter = infix "∩" ;
    Add = infix "+" ;
    Minus = infix "−" ;
    Mul = infix "·" ;
    Div = infix "/" ;
    Pow = infix "^" ;
    Neg a = simple (glue "−" (tight a)) ;
    Cast a = simple (glue "↑" (tight a)) ;
    Lam x b = simple (paren (x ++ "↦" ++ b.s)) ;
    -- A function whose argument the body does not use shows the argument's type.
    LamTy x t b = simple (paren (x ++ "∈" ++ t.sym ++ "↦" ++ b.s)) ;
    LamP x p = described ("the property" ++ x ++ "↦" ++ p.s) ;
    FirstTerms n s t = simple (braces (glue s (paren n) ++ ":" ++ n ++ "<" ++ t)) ;
    -- Braces only over a type with a symbol; otherwise words, so "{i ∈ C : P}" always means a set C.
    SetOfTy x t p = case t.has of {
        HasSym => simple (braces (x ++ t.bind ++ ":" ++ p.s)) ;
        NoSym => described ("the set of" ++ t.pl ++ x ++ t.compl ++ "such that" ++ p.s) } ;
    SetOfOutside x t a p = case t.has of {
        HasSym => simple (braces (x ++ t.bind ++ "∖" ++ tight a ++ ":" ++ p.s)) ;
        NoSym => described ("the set of" ++ t.pl ++ x ++ t.compl ++ "outside" ++ tight a ++ "such that" ++ p.s) } ;
    FilterSet i a p = simple (braces (i ++ "∈" ++ tight a ++ ":" ++ p.s)) ;
    KMGenerator f = described ("the membership-query generator for" ++ f.s) ;
    PromptedGenerator f e = described ("the prompted membership-query generator for" ++ f.s ++ "with coding" ++ e) ;
    RunAt g s t = described ("the output of" ++ g ++ "on" ++ s ++ "at step" ++ t) ;
    RunPromptedAt g s q t = described ("the output of" ++ g ++ "on" ++ s ++ "and" ++ q ++ "at step" ++ t) ;
    Pair a b = simple (paren (operand a ++ comma ++ operand b)) ;
    UnitT = simple ("(" ++ "GLUE" ++ ")") ;
    ListNil = simple ("[" ++ "GLUE" ++ "]") ;
    ListOf xs = simple (glue (glue "[" xs) "]") ;
    -- An element of a subtype, such as C(z) as an element of the range of C.
    Elem a = simple (glue (glue "⟨" (operand a)) "⟩") ;
    -- A finite set where a set is expected.
    FinsetSet a = described ("the set" ++ operand a) ;
    OneArg a = operand a ;
    MoreArgs a xs = operand a ++ comma ++ xs ;

    Mem = relation "∈" ;
    NotMem = relation "∉" ;
    Sub = relation "⊆" ;
    NotSub = relation "⊈" ;
    Eq = relation "=" ;
    Ne = relation "≠" ;
    Le = relation "≤" ;
    Lt = relation "<" ;
    Ge = relation "≥" ;
    Gt = relation ">" ;
    CardAtLeast s n = atom (glue (glue "|" (operand s)) "|" ++ "≥" ++ operand n) ;
    LengthAtLeast c n = atom (operand c ++ "has length at least" ++ operand n) ;
    IsPrefix p w = atom (operand p ++ "is a prefix of" ++ operand w) ;
    ValuesExactly f a = worded "the set of values of" "The set of values of" (f ++ "is exactly" ++ operand a) Atom ;
    ValuesIn f a = worded "every value of" "Every value of" (f ++ "lies in" ++ operand a) Atom ;
    Injective f = atom (f ++ "is injective") ;
    Confirms f x i = worded "the oracle confirms" "The oracle confirms" (operand x ++ "∈" ++ sub f.lang i) Atom ;
    Holds x a = atom (operand x ++ "is" ++ a) ;
    IsLbl x l = case l.v of { Copular => atom (operand x ++ "is" ++ l.s) ; Verb => atom (operand x ++ l.s) } ;
    IsNotLbl x l = case l.v of {
        Copular => atom (operand x ++ "is not" ++ l.s) ;
        Verb => worded "it is false that" "It is false that" (operand x ++ l.s) Quant } ;
    LblHolds l xs = atom (glue l.s (paren xs)) ;
    LblFails l xs = fails (glue l.s (paren xs)) ;
    LblProp l = atom (l.s ++ "holds") ;
    VarHolds f xs = atom (glue f (paren xs)) ;
    VarFails f xs = fails (glue f (paren xs)) ;
    VarProp v = atom v ;
    And p q = {s = left p ++ "and" ++ rightOf Conj q ; c = leftC p ++ "and" ++ rightOf Conj q ; k = Conj} ;
    Or p q = {s = left p ++ "or" ++ rightOf Disj q ; c = leftC p ++ "or" ++ rightOf Disj q ; k = Disj} ;
    Iff p q = {s = left p ++ "if and only if" ++ rightOf Cond q ; c = leftC p ++ "if and only if" ++ rightOf Cond q ;
               k = Cond} ;
    Imp p q = worded "if" "If" (left p ++ comma ++ "then" ++ q.s) Cond ;
    Not p = worded "it is not the case that" "It is not the case that" p.s Quant ;
    -- A quantifier follows an atomic claim and precedes any other claim.
    ForallIn x a p = case p.k of {
        Atom => {s = p.s ++ "for every" ++ x ++ "∈" ++ operand a ; c = p.c ++ "for every" ++ x ++ "∈" ++ operand a ;
                 k = Post} ;
        _ => worded "for every" "For every" (x ++ "∈" ++ operand a ++ comma ++ p.s) Quant } ;
    ForallAtLeast x lo p = worded "for every" "For every" (x ++ "≥" ++ operand lo ++ comma ++ p.s) Quant ;
    ForallOne x t p = case p.k of {
        Atom => {s = p.s ++ "for every" ++ bare x t ; c = p.c ++ "for every" ++ bare x t ; k = Post} ;
        _ => worded "for every" "For every" (bare x t ++ comma ++ p.s) Quant } ;
    ForallMany ns t p = worded "for all" "For all" (t.pl ++ ns.s ++ t.compl ++ comma ++ p.s) Quant ;
    ExistsSuch x t p = worded "there is" "There is" (some x t ++ "such that" ++ p.s) Quant ;
    NoneSuch x t p = worded "there is no" "There is no" (bare x t ++ "such that" ++ p.s) Quant ;
    ExistsIn x a p = worded "there is" "There is" (x ++ "∈" ++ operand a ++ "such that" ++ p.s) Quant ;
    ExistsGe x lo p = worded "there is" "There is" (x ++ "≥" ++ operand lo ++ "such that" ++ p.s) Quant ;
    ForallBelow x hi p = case p.k of {
        Atom => {s = p.s ++ "for every" ++ x ++ "<" ++ operand hi ; c = p.c ++ "for every" ++ x ++ "<" ++ operand hi ;
                 k = Post} ;
        _ => worded "for every" "For every" (x ++ "<" ++ operand hi ++ comma ++ p.s) Quant } ;
    ExistsBelow x hi p = worded "there is" "There is" (x ++ "<" ++ operand hi ++ "such that" ++ p.s) Quant ;
    Frequently x p = case p.k of {
        Atom => {s = p.s ++ "for infinitely many" ++ x ++ "∈" ++ "ℕ" ;
                 c = p.c ++ "for infinitely many" ++ x ++ "∈" ++ "ℕ" ; k = Post} ;
        _ => worded "for infinitely many" "For infinitely many" (x ++ "∈" ++ "ℕ" ++ comma ++ p.s) Quant } ;
    Eventually x p = worded "for all sufficiently large" "For all sufficiently large" (x ++ "∈" ++ "ℕ" ++ comma ++ p.s) Quant ;

    LongExtensions f = "has arbitrarily long extensions in every" ++ sub f.lang "i" ;
}
