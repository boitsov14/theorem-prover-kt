# theorem-prover-kt

## Description

A sequent-style theorem prover for first-order logic implemented in Kotlin.

## Rust rewrite
I am rewriting this project in Rust. See [theorem-prover-rs](https://github.com/boitsov14/theorem-prover-rs).

## [Demo site](https://boitsov14.github.io/web-prover/)

## Misskey bot

[@sequent_bot@misskey.io](https://misskey.io/@sequent_bot)

## Twitter bot

[@sequent_bot](https://twitter.com/sequent_bot)

## How to use

```
git clone https://github.com/boitsov14/theorem-prover-kt.git
cd theorem-prover-kt
chmod +x gradlew
./gradlew shadowJar
java -jar build/libs/theorem-prover-kt-all.jar "∃x∀yP(x,y) → ∀y∃xP(x,y)"
latex out.tex
dvipng out.dvi
```

## APIs

[api-for-theorem-prover](https://github.com/boitsov14/api-for-theorem-prover)

## Special Thanks

- [Build Your Own First-Order Prover](http://jens-otten.de/tutorial_cade19)
- [stepchowfun/theorem-prover](https://github.com/stepchowfun/theorem-prover)
- [qnighy/ipc_solver](https://github.com/qnighy/ipc_solver)
