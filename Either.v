Inductive Either (A B : Set) : Set :=
| Left : A -> Either A B
| Right : B -> Either A B.

Function Eapp {A B C : Set} (f : A -> Either C B) (g : Either C A) : Either C B :=
  match g with
    | Left x => Left C B x
    | Right x =>
      match (f x) with
        | Left x => Left C B x
        | Right x => Right C B x
      end
  end.

Function NEapp {A B C : Set} (f : A -> B) (g : Either C A) : Either C B :=
  match g with
    | Left x => Left _ _ x
    | Right z => Right _ _ (f z)
  end.
