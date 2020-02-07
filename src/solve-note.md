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

# Lab1

## Haskell environment

> vim ~/.stack/config.yaml
>
> #add
>
> setup-info: "http://mirrors.ustc.edu.cn/stackage/stack-setup.yaml"
> urls:
>   latest-snapshot: http://mirrors.ustc.edu.cn/stackage/snapshots.json
>   lts-build-plans: http://mirrors.ustc.edu.cn/stackage/lts-haskell/
>   nightly-build-plans: http://mirrors.ustc.edu.cn/stackage/stackage-nightly/

use ustc open source to acclerate download.

# Lab2

BadBlock disk is an application using CHL framework

BadBlock disk has an extra block at the tail and an extra attribute "bad block id". "bad block id" points out a block in the disk and whenever we read the bad block, we get the content of the last block.