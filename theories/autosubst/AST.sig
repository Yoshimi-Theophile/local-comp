-- Universe levels
level : Type
sort : Type

-- Syntax

term(var) : Type

Sort : sort -> level -> term

Pi : sort -> sort -> term -> (bind term in term) -> term
lam : sort -> sort -> term -> (bind term in term) -> term
app : sort -> sort -> term -> term -> term

unit : level -> term
tt : level -> term

Sigma : term -> (bind term in term) -> term
sig : term -> (bind term in term) -> term
pi1 : term -> term
pi2 : term -> term