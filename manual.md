# Manual / マニュアル

## Parser / パーサー

- Binary Connectives are all right-associative.
<br> 二項結合子はすべて右結合．

    example: P → Q → R := P → (Q → R)

- The precedence of logical connectives
<br> 論理結合子の優先度

    |Precedence|Logical Connective|
    |-|-|
    |4|¬, ∀, ∃|
    |3|∧|
    |2|∨|
    |1|→|
    |0|↔|

    example: P ∧ Q ∨ R := (P ∧ Q) ∨ R

- The parsable expression of non-logical symbols
<br> 非論理記号のパース可能な表現

    |Non-logical<br>Symbol|Regular<br>Expression|Acceptable<br>Examples|Unacceptable<br>Examples|
    |-|-|-|-|
    |Proposition<br>Predicate<br>Free Variable|[a-zA-Zα-ωΑ-Ω\d]+|P<br>123VeryLongName123<br>αβγ|P_1|
    |Bounded Variable|[a-zA-Zα-ωΑ-Ω]\d*|x<br>x123<br>α|xyz<br>x_1<br>123x123

- The syntax sugar of logical symbols
<br> 論理記号の糖衣構文

    |Logical<br>Symbol|Syntax Sugars|
    |-|-|
    |⊢|proves, vdash, \vdash, \|-, ├, ┣|
    |⊤|true, tautology, top, \top|
    |⊥|false, contradiction, bottom, bot, \bot|
    |¬|not, ~, negation, lnot, \lnot, neg, \neg|
    |∧|and, land, \land, /\\, &, &&, wedge, \wedge|
    |∨|or, lor, \lor, \\/, \|, \|\|, vee, \vee|
    |→|to, \to, imp, \imp, implies, imply, ->, =>, -->, ==>, ⇒, rightarrow, \rightarrow|
    |↔|iff, \iff, <->, <=>, <-->, <==>, ⇔, ≡, if and only if, leftrightarrow, \leftrightarrow, equiv, equivalent|
    |∀|forall, \forall, all, for all, !|
    |∃|exists, \exists, ex, there exists, ?|
    |()|{}, []|

    example: all x [P(x) and Q] to all x P(x) and Q := ∀x(P(x) ∧ Q) → (∀xP(x) ∧ Q)

- A sequence of the same quantifiers can be omitted.
<br> 同じ量化子の連続は省略可能．

    example: ∀x, y, z P(x) := ∀x∀y∀z P(x)

- The meanings of parse error messages
<br> パースエラーメッセージの解説

    |Error Message|Meaning|Examples|
    |-|-|-|
    |Parenthesis Error.|Mismatch in number of<br> left/right brackets<br>左右括弧の不一致|((P → Q)|
    |Duplicated Bounded Variables||∀x∃y∀x P(x,y)|
    |Cannot Quantify Predicate||∀P (P → P)|
    |Cannot Quantify Function||∀f (Q → P(f(x)))|
    |The quantifier must be used<br> in the form '∀x'||∀(P(x))|
    |The quantifier must be used<br> in the form '∃x'||∃(P(x))|
    |⊢ must occur one time.|||
    |Illegal Argument|||
    |Parse Error.|other parse error<br>その他のパースエラー|P ∧∧ Q|

## Reply messages / リプライメッセージ

- The meanings of reply messages
<br> リプライメッセージの解説

    |Error Message|Meaning|
    |-|-|
    |Provable.||
    |Unprovable.||
    |Proof Failed: Too many unification terms.||
    |Proof Failed: Timeout.||
    |The proof tree is too large to output: Timeout.||
    |Proof Failed: OutOfMemoryError.||
    |The proof tree is too large to output: OutOfMemoryError.||
    |Proof Failed: StackOverflowError.||
    |An unexpected error has occurred: Java exec failure.||
    |The proof tree is too large to output: Dimension too large.||
    |An unexpected error has occurred: Could not compile tex file.||
    |The proof tree is too large to output: DVI stack overflow.||
    |An unexpected error has occurred: Could not compile dvi file.||
