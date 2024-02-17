In Jan 2024 I played around with the Lean theorem prover. Lean is designed to formalize math proofs. Different people have different "goals and dreams" for Lean, but one big goal is to make research-level math easy to formalize, and the "dream" is that it's so easy that math researchers formalize their proofs as a matter of course (e.g. a journal won't accept a claimed proof of a theorem unless it's been formalized). From this angle, some benefits are

1. We're more confident that published results are correct
1. Researchers can collaborate in larger groups [the idea is that currently, you can't really use a lemma someone proved as a "black box" without doing the expensive work of verifying it yourself, because it may be incorrect or have subtle hidden assumptions, and you'll mis-apply it by treating it like a black box]
1. The math literature becomes more easily searchable

Link to Tao's video

Some other people, mostly software engineers / CS folks, have another "goal" which is to make it easy to prove that software behaves correctly, and easy to specify what "behaves correctly" means. The "dream" is that when reviewing code, we don't just say "this looks correct to me" (which is basically what we do now), we can read the specification and have the computer check that the program matches the spec. HtDP, Software Foundations

This goal is actually broader than it might appear at first glance; you can think of a static type system (e.g. how variables have types in Java, but not in Python) as a kind of proof of correctness (a proof that the Java program won't try to add an integer and a string the same way a python program might). The rust type system (in the form of ownership / borrow checker) can also be seen as a proof of correctness (e.g. memory safety, concurrency). As the examples suggest, most programming languages encode these into their type systems, which is why the more "modern/expressive" type system features (think: generics, monads, rust, https://learn.microsoft.com/en-us/dotnet/csharp/programming-guide/generics/constraints-on-type-parameters); they're letting the programmer prove more things or write shorter proofs. 

My personal goals are a mix from both of these

1. Learn how can math proofs be formalized, and what difficulties come up in practice when you try to do this
1. See what analogies there are between the software engineering challenge of "organizing a large codebase" and "organizing a large collection of theorems and definitions" (Lean's math library is called mathlib and it's basically one giant library for everything from the )
1. Learn type theory, a kind of foundational axiom system that lots of theorem provers use as an alternative to set theory, why they choose to do this, and what variants there are
1. Learn a dependently typed programming language

How's it going?

Math side: I learned how to formalise stuff like "sum converge", how to state things, what kinds of things are difficult / easy to prove. Example from Abbott.

I learned that "IDE support" and automation is really important, actually a lot more so than in software engineering. Tactics, normal form. Ring macro.

I learned that a lot of mathlib is written in very high generality.

There's a multilayer analogy to software engineering. lst[1] = lst.

It's like learning a new programming language. There's a big vocabulary of stuff to learn, much of which depends on each other, and you can get stuck for stupid reasons. The proofs get cleaner.

Type theory: section 4 is really quite eye opening. Key points

I always thought in type theory, t : T is like t \subset T, because I'm so used to set theory. If t : R, and we want to say t is even, I would have guessed t : 2R in anallogy to set theory. Actually this is illegal; the typing judgement behaves a lot like in PL, where it's illegal to have a value have two types. The actual way is t \subset s : Prop. Set s has type Set T. It's very close to programming languages. I wish the intro material talked about this more

Quality of teaching material

Hopefully it converges
