# Lab0

## "function call"

Definition/Fixpoint fun_name : proc unit := line1; line2; line3; Ret tt.

## "function spec"

Theorem fun\_name\_ok : pre ... post ... recovered ...

## "Code"

vars.read / vars.write / <func call>
every line should have a return value (maybe \_, like (\_ <- xxx) 

## code proof

1. To go forward, use Ltac step_proc to go forward a line.
2. **Importantly**, step\_proc can only resolve function call which has "Hint Resolve xxx\_ok" and "Opaque xxx" 
