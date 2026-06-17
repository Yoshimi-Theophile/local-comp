-- Universe levels
level : Type
sort : Type

-- Syntax

term(var) : Type

Sort : sort -> level -> term

Pi : sort -> sort -> term -> (bind term in term) -> term
lam : sort -> sort -> term -> (bind term in term) -> term
app : sort -> sort -> term -> term -> term
