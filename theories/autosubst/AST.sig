-- Universe levels
level : Type
sort : Type

-- Syntax

term(var) : Type

Sort : sort -> level -> term

Pi : term -> (bind term in term) -> term
lam : term -> (bind term in term) -> term
app : term -> term -> term
