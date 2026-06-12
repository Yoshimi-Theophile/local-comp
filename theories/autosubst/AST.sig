-- Universe levels
level : Type

-- Syntax

term(var) : Type

Typ : level -> term
PTyp : level -> term

Pi : term -> (bind term in term) -> term
lam : term -> (bind term in term) -> term
app : term -> term -> term
