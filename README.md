# Jadeo

Jadeo is a relational-functional reflective tower, with relational (miniKanren) levels and functional (Scheme) levels stacked in the tower. The source code is in ``jadeo.scm``.

## Key Features

After loading ``jadeo.scm``, Jadeo can be used through a ternary miniKanren relation ``runo``, which is a relational version of the ``run`` function for miniKanren. The first argument to ``runo`` corresponds to how many answers to take as a peano numeral, the second should be a Jadeo expression, and the third should be the result of evaluating the Jadeo expression and taking results according to the first argument.

A Jadeo expression mixes up miniKanren and Scheme parts using reifiers and reflectors. In a miniKanren level, one can go up to another miniKanren metalevel by the ``muo`` reifier, and one can go up to a Scheme metalevel by the ``muos`` reifier. In the Scheme level, one can go up to a miniKanren level by the ``muso`` reifier. The tower is structured as repetitions of miniKanren, miniKanren, and Scheme levels, so these are the three cases that can occur.

Other than reifiers, we also have reflectors like ``meaning-mk`` and ``meaning-scm``, which takes in expressions, substitution-counter pair (for ``meaning-mk``), reified enironment, reified store, reified continuation, and generates a new level based on these input. There is also a relational version of ``meaning-scm``, ``meaning-scmo``, that additionally takes an argument for unifying with the result returned by the new Scheme level. The reflector ``meaning`` is a generalization of the common ``eval`` special form, and we achieve the behaviour of ``eval`` through generating new levels, which gives us two extra reflectors ``eval-scm`` and ``eval-mk``. Finally we also have ``new-scm`` and ``new-mk``, which are like eval, but evaluates input expression not under the current environment, store, and continuation, but under completely new initial environment, new initial store, and identity continuation. They are similar to the``open-level`` fsubr found in Blond.

The following table summarizes the key reifiers and reflectors of Jadeo:
| name                          | description                                                                                        |
|-------------------------------|----------------------------------------------------------------------------------------------------|
| `(muo (e s/c r st k) gexp)`   | reifier from miniKanren to miniKanren                                                              |
| `(muos (e s/c r st k) exp)`   | reifier from miniKanren to Scheme                                                                  |
| `(muso (e r st k) gexp)`      | reifier from Scheme to miniKanren                                                                  |
| `(meaning-mk e s/c r st k)`   | reflector for making new miniKanren level                                                          |
| `(meaning-scm e r st k)`      | reflector for making new scheme level                                                              |
| `(meaning-scmo e r st k out)` | relational reflector for making new scheme level                                                   |
| `(eval-mk ge)`                | reflector using current environment and continuation as env and cont of a new relational level     |
| `(eval-scm e)`                | like eval-mk, but takes Scheme expressions, and change environment to contain Scheme default fsubr |
| `(eval-scmo e out)`           | relational version of eval-scmo                                                                    |
| `(new-scm e)`                 | like eval-scm, but uses initial environment, store, and continuation to evaluate expression        |
| `(new-mk ge)`                 | like new-scm, but evaluates a miniKanren expression                                                |


Other than the key features, we also have a few Blond like constructs for dealing with reified continuations and reified environments. The special forms ``apply-cont-jmp`` and ``apply-cont-psh`` take in a reified continuation and an argument, and continues with the reified continuation by supplying the argument provided. The former discards the curent continuation while the latter pushes the current continuation of current level onto the tower.
| name                       | description                                                                                  |
|----------------------------|----------------------------------------------------------------------------------------------|
| `(apply-cont-jmp k e)`     | same as jumpy way of applying reified continuation in Blond                                  |
| `(apply-cont-psh k e)`     | same as pushy way of applying reified continuation in Blond                                  |
| `(add-exit-lv-conto k k^)` | relation that relates a reified continuation with a modified one that exit level at the end  |
| `(rei-lookup e r st)`      | function taking a symbol and reified environment and store, returns value of symbol in store |



## Example Use Cases

In the following example, we use ``run`` to run miniKanren inside Scheme, then run Jadeo via the ``runo`` relation.
We first introduce fresh variables `a`, `b`, `c`, and `d` in level 0, then use `muo` to go up to level 1. The reifier `muo` reifies the substitution-counter pair, environment, store, and continuation at level 0 when it is invoked.

This means the expression `(conj (==mk 42 d) (==mk c (d (d 3))))` is bound to the symbol `e` at level 1, and the remaining continuation that requires a conjunction with relations ` (==mk (d b) c)` and `(==mk a (c b)` into symbol `k`, and environment and store containing the variables `a`,  `b`, `c`, and `d` bound to symbols `r` and `st`.

In level 1, we first use `==mk` to unify the new fresh variable generated at level 1 with `e`, which stores the expression `(conj (==mk 42 d) (==mk c (d (d 3))))`. Then we use the reflector `meaning-mk` to reopen a miniKanren level, going back to level 0. In level 0, we first evaluate `(conj (==mk 42 d) (==mk c (d (d 3))))`, then bind the resulting stream to expressions `(==mk (d b) c)` and `(==mk a (c b))`.

After evaluation of expression is done, we now have 42 unified to the variable denoted by `d`, `c` to `(d (d 3))` thus `(42 (42 3))`, `b` to `(42 3)`, and `a` to  `((42 (42 3)) (42 3))`. `runo` would take all possible output for `a`, the first variable introduced by `fresh`, and since there is only one answer, `((42 (42 3)) (42 3))` is the final result we get. Since this result comes from level 0, we use the peano representation of level 0, the empty list, to denote the level.
	
```
> (run 1 (out) (runo 'all
			 '(fresh (a b c d)
				 ((muo (e s/c r st k)
				       (fresh (tm)
					      (==mk tm e)
					      (meaning-mk tm s/c r st k)
					      ))
				  conj (==mk 42 d) (==mk c (d (d 3)))
				  )
				 (==mk (d b) c)
				 (==mk a (c b))
				 ) out))
				 
((level: () result: (((42 (42 3)) (42 3)))))
```

## Run Tests

To run tests, open any scheme repl and enter `` (load "jadeo.scm") `` to load Jadeo,
then enter `` (run-tests) `` to run the tests.

To turn on tracing for tests, enter ``(trace-on)`` in repl.

To turn off tracing, enter ``(trace-off)``.
