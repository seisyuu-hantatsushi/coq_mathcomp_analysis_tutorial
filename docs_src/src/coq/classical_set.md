# Coqでの古典集合
## mathcomp
### 外包的記法
```coq
Inductive Fruits : Type :=
| Apple
| Orange
| PineApple
| Mango.
```
### 内包的記法
```coq
  Definition IsMyFruits (fruits : Fruits) : Prop :=
    match fruits with
    | Apple => True
    | Orange => True
    | Mango => True
    | _ => False
    end.
```
