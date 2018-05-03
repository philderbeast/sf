---
title     : "Relations: Inductive definition of relations"
layout    : page
permalink : /Relations
---

After having defined operations such as addition and multiplication,
the next step is to define relations, such as *less than or equal*.


## Imports

<pre class="Agda">{% raw %}<a id="273" class="Keyword">import</a> <a id="280" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="318" class="Symbol">as</a> <a id="321" class="Module">Eq</a>
<a id="324" class="Keyword">open</a> <a id="329" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="332" class="Keyword">using</a> <a id="338" class="Symbol">(</a><a id="339" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="342" class="Symbol">;</a> <a id="344" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="348" class="Symbol">;</a> <a id="350" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#981" class="Function">cong</a><a id="354" class="Symbol">;</a> <a id="356" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function">sym</a><a id="359" class="Symbol">)</a>
<a id="361" class="Keyword">open</a> <a id="366" class="Keyword">import</a> <a id="373" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="382" class="Keyword">using</a> <a id="388" class="Symbol">(</a><a id="389" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="390" class="Symbol">;</a> <a id="392" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="396" class="Symbol">;</a> <a id="398" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="401" class="Symbol">;</a> <a id="403" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="406" class="Symbol">;</a> <a id="408" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator">_*_</a><a id="411" class="Symbol">;</a> <a id="413" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#320" class="Primitive Operator">_∸_</a><a id="416" class="Symbol">)</a>
<a id="418" class="Keyword">open</a> <a id="423" class="Keyword">import</a> <a id="430" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="450" class="Keyword">using</a> <a id="456" class="Symbol">(</a><a id="457" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8101" class="Function">+-comm</a><a id="463" class="Symbol">;</a> <a id="465" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7665" class="Function">+-suc</a><a id="470" class="Symbol">)</a>{% endraw %}</pre>


## Defining relations

The relation *less than or equal* has an infinite number of
instances.  Here are a few of them:

    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

And here is the definition in Agda:
<pre class="Agda">{% raw %}<a id="1147" class="Keyword">data</a> <a id="_≤_"></a><a id="1152" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">_≤_</a> <a id="1156" class="Symbol">:</a> <a id="1158" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1160" class="Symbol">→</a> <a id="1162" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1164" class="Symbol">→</a> <a id="1166" class="PrimitiveType">Set</a> <a id="1170" class="Keyword">where</a>
  <a id="_≤_.z≤n"></a><a id="1178" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a> <a id="1182" class="Symbol">:</a> <a id="1184" class="Symbol">∀</a> <a id="1186" class="Symbol">{</a><a id="1187" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1187" class="Bound">m</a> <a id="1189" class="Symbol">:</a> <a id="1191" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1192" class="Symbol">}</a> <a id="1194" class="Symbol">→</a> <a id="1196" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="1201" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="1203" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1187" class="Bound">m</a>
  <a id="_≤_.s≤s"></a><a id="1207" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="1211" class="Symbol">:</a> <a id="1213" class="Symbol">∀</a> <a id="1215" class="Symbol">{</a><a id="1216" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1216" class="Bound">m</a> <a id="1218" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1218" class="Bound">n</a> <a id="1220" class="Symbol">:</a> <a id="1222" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1223" class="Symbol">}</a> <a id="1225" class="Symbol">→</a> <a id="1227" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1216" class="Bound">m</a> <a id="1229" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="1231" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1218" class="Bound">n</a> <a id="1233" class="Symbol">→</a> <a id="1235" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1239" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1216" class="Bound">m</a> <a id="1241" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="1243" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1247" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1218" class="Bound">n</a>{% endraw %}</pre>
Here `z≤n` and `s≤s` (with no spaces) are constructor names,
while `m ≤ m`, and `m ≤ n` and `suc m ≤ suc n` (with spaces)
are types.  This is our first use of an *indexed* datatype,
where we say the type `m ≤ n` is indexed by two naturals, `m` and `n`.

Both definitions above tell us the same two things:

+ *Base case*: for all naturals `n`, the proposition `zero ≤ n` holds
+ *Inductive case*: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

+ *Base case*: for all naturals `n`, the constructor `z≤n` 
  produces evidence that `zero ≤ n` holds.
+ *Inductive case*: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

For example, here in inference rule notation is the proof that
`2 ≤ 4`.

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof.
<pre class="Agda">{% raw %}<a id="2299" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#2299" class="Function">_</a> <a id="2301" class="Symbol">:</a> <a id="2303" class="Number">2</a> <a id="2305" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="2307" class="Number">4</a>
<a id="2309" class="Symbol">_</a> <a id="2311" class="Symbol">=</a> <a id="2313" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="2317" class="Symbol">(</a><a id="2318" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="2322" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a><a id="2325" class="Symbol">)</a>{% endraw %}</pre>


## Implicit arguments

This is our first use of implicit arguments.
In the definition of inequality, the two lines defining the constructors
use `∀`, very similar to our use of `∀` in propositions such as:

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }` rather than
parentheses `( )`.  This means that the arguments are *implicit* and need not be
written explicitly; instead, they are *inferred* by Agda's typechecker. Thus, we
write `+-comm m n` for the proof that `m + n ≡ n + m`, but `z≤n` for the proof
that `m ≤ m`, leaving `m` implicit.  Similarly, if `m≤n` is evidence that `m ≤
n`, we write write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving both `m`
and `n` implicit.

If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit.
<pre class="Agda">{% raw %}<a id="3320" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#3320" class="Function">_</a> <a id="3322" class="Symbol">:</a> <a id="3324" class="Number">2</a> <a id="3326" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="3328" class="Number">4</a>
<a id="3330" class="Symbol">_</a> <a id="3332" class="Symbol">=</a> <a id="3334" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="3338" class="Symbol">{</a><a id="3339" class="Number">1</a><a id="3340" class="Symbol">}</a> <a id="3342" class="Symbol">{</a><a id="3343" class="Number">3</a><a id="3344" class="Symbol">}</a> <a id="3346" class="Symbol">(</a><a id="3347" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="3351" class="Symbol">{</a><a id="3352" class="Number">0</a><a id="3353" class="Symbol">}</a> <a id="3355" class="Symbol">{</a><a id="3356" class="Number">2</a><a id="3357" class="Symbol">}</a> <a id="3359" class="Symbol">(</a><a id="3360" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a> <a id="3364" class="Symbol">{</a><a id="3365" class="Number">2</a><a id="3366" class="Symbol">}))</a>{% endraw %}</pre>


## Precedence

We declare the precedence for comparison as follows.
<pre class="Agda">{% raw %}<a id="3464" class="Keyword">infix</a> <a id="3470" class="Number">4</a> <a id="3472" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">_≤_</a>{% endraw %}</pre>
We set the precedence of `_≤_` at level 4, so it binds less tightly
that `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.


## Decidability

Given two numbers, it is straightforward to compute whether or not the first is
less than or equal to the second.  We don't give the code for doing so here, but
will return to this point in Chapter [Decidability](Decidability).


## Properties of ordering relations

Relations occur all the time, and mathematicians have agreed
on names for some of the most common properties.

+ *Reflexive* For all `n`, the relation `n ≤ n` holds.
+ *Transitive* For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
+ *Anti-symmetric* For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
+ *Total* For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

The relation `_≤_` satisfies all four of these properties.

There are also names for some combinations of these properties.

+ *Preorder* Any relation that is reflexive and transitive.
+ *Partial order* Any preorder that is also anti-symmetric.
+ *Total order* Any partial order that is also total.

If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.

Less frivolously, if you ever bump into a relation while reading
a technical paper, this gives you an easy way to orient yourself,
by checking whether or not it is a preorder, partial order, or total order.
A careful author will often make it explicit, for instance by saying
that a given relation is a preorder but not a partial order, or a
partial order but not a total order. (Can you think of examples of
such relations?)


## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.
<pre class="Agda">{% raw %}<a id="≤-refl"></a><a id="5623" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#5623" class="Function">≤-refl</a> <a id="5630" class="Symbol">:</a> <a id="5632" class="Symbol">∀</a> <a id="5634" class="Symbol">{</a><a id="5635" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#5635" class="Bound">n</a> <a id="5637" class="Symbol">:</a> <a id="5639" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="5640" class="Symbol">}</a> <a id="5642" class="Symbol">→</a> <a id="5644" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#5635" class="Bound">n</a> <a id="5646" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="5648" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#5635" class="Bound">n</a>
<a id="5650" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#5623" class="Function">≤-refl</a> <a id="5657" class="Symbol">{</a><a id="5658" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="5662" class="Symbol">}</a> <a id="5664" class="Symbol">=</a> <a id="5666" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a>
<a id="5670" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#5623" class="Function">≤-refl</a> <a id="5677" class="Symbol">{</a><a id="5678" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5682" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#5682" class="Bound">n</a><a id="5683" class="Symbol">}</a> <a id="5685" class="Symbol">=</a> <a id="5687" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="5691" class="Symbol">(</a><a id="5692" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#5623" class="Function">≤-refl</a> <a id="5699" class="Symbol">{</a><a id="5700" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#5682" class="Bound">n</a><a id="5701" class="Symbol">})</a>{% endraw %}</pre>
The proof is a straightforward induction on `n`.  In the base case,
`zero ≤ zero` holds by `z≤n`.  In the inductive case, the inductive
hypothesis `≤-refl n` gives us a proof of `n ≤ n`, and applying `s≤s`
to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `^C ^C`, `^C ^,`, and `^C ^R` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤
p` hold, then `m ≤ p` holds.
<pre class="Agda">{% raw %}<a id="≤-trans"></a><a id="6281" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6281" class="Function">≤-trans</a> <a id="6289" class="Symbol">:</a> <a id="6291" class="Symbol">∀</a> <a id="6293" class="Symbol">{</a><a id="6294" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6294" class="Bound">m</a> <a id="6296" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6296" class="Bound">n</a> <a id="6298" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6298" class="Bound">p</a> <a id="6300" class="Symbol">:</a> <a id="6302" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="6303" class="Symbol">}</a> <a id="6305" class="Symbol">→</a> <a id="6307" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6294" class="Bound">m</a> <a id="6309" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="6311" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6296" class="Bound">n</a> <a id="6313" class="Symbol">→</a> <a id="6315" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6296" class="Bound">n</a> <a id="6317" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="6319" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6298" class="Bound">p</a> <a id="6321" class="Symbol">→</a> <a id="6323" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6294" class="Bound">m</a> <a id="6325" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="6327" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6298" class="Bound">p</a>
<a id="6329" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6281" class="Function">≤-trans</a> <a id="6337" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a> <a id="6341" class="Symbol">_</a> <a id="6343" class="Symbol">=</a> <a id="6345" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a>
<a id="6349" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6281" class="Function">≤-trans</a> <a id="6357" class="Symbol">(</a><a id="6358" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="6362" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6362" class="Bound">m≤n</a><a id="6365" class="Symbol">)</a> <a id="6367" class="Symbol">(</a><a id="6368" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="6372" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6372" class="Bound">n≤p</a><a id="6375" class="Symbol">)</a> <a id="6377" class="Symbol">=</a> <a id="6379" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="6383" class="Symbol">(</a><a id="6384" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6281" class="Function">≤-trans</a> <a id="6392" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6362" class="Bound">m≤n</a> <a id="6396" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6372" class="Bound">n≤p</a><a id="6399" class="Symbol">)</a>{% endraw %}</pre>
Here the proof is most easily thought of as by induction on the
*evidence* that `m ≤ n`, so we have left `m`, `n`, and `p` implicit.

In the base case, the first inequality holds by `z≤n`, and so
we are given `zero ≤ n` and `n ≤ p` and must show `zero ≤ p`,
which follows immediately by `z≤n`.  In this
case, the fact that `n ≤ p` is irrelevant, and we write `_` as the
pattern to indicate that the corresponding evidence is unused.

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.

<!--

In the base case, `m ≤ n` holds by `z≤n`, so it must be that
`m` is `zero`, in which case `m ≤ p` also holds by `z≤n`. In this
case, the fact that `n ≤ p` is irrelevant, and we write `_` as the
pattern to indicate that the corresponding evidence is unused.

In the inductive case, `m ≤ n` holds by `s≤s m≤n`, so it must be that `m`
is `suc m′` and `n` is `suc n′` for some `m′` and `n′`, and `m≤n` is
evidence that `m′ ≤ n′`.  In this case, the only way that `p ≤ n` can
hold is by `s≤s n≤p`, where `p` is `suc p′` for some `p′` and `n≤p` is
evidence that `n′ ≤ p′`.  The inductive hypothesis `≤-trans m≤n n≤p`
provides evidence that `m′ ≤ p′`, and applying `s≤s` to that gives
evidence of the desired conclusion, `suc m′ ≤ suc p′`.

-->

The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that
such a case cannot arise, and does not require it to be listed.

Alternatively, we could make the implicit parameters explicit.
<pre class="Agda">{% raw %}<a id="≤-trans′"></a><a id="8223" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8223" class="Function">≤-trans′</a> <a id="8232" class="Symbol">:</a> <a id="8234" class="Symbol">∀</a> <a id="8236" class="Symbol">(</a><a id="8237" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8237" class="Bound">m</a> <a id="8239" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8239" class="Bound">n</a> <a id="8241" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8241" class="Bound">p</a> <a id="8243" class="Symbol">:</a> <a id="8245" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="8246" class="Symbol">)</a> <a id="8248" class="Symbol">→</a> <a id="8250" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8237" class="Bound">m</a> <a id="8252" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="8254" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8239" class="Bound">n</a> <a id="8256" class="Symbol">→</a> <a id="8258" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8239" class="Bound">n</a> <a id="8260" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="8262" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8241" class="Bound">p</a> <a id="8264" class="Symbol">→</a> <a id="8266" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8237" class="Bound">m</a> <a id="8268" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="8270" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8241" class="Bound">p</a>
<a id="8272" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8223" class="Function">≤-trans′</a> <a id="8281" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="8286" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8286" class="Bound">n</a> <a id="8288" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8288" class="Bound">p</a> <a id="8290" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a> <a id="8294" class="Symbol">_</a> <a id="8296" class="Symbol">=</a> <a id="8298" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a>
<a id="8302" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8223" class="Function">≤-trans′</a> <a id="8311" class="Symbol">(</a><a id="8312" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8316" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8316" class="Bound">m</a><a id="8317" class="Symbol">)</a> <a id="8319" class="Symbol">(</a><a id="8320" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8324" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8324" class="Bound">n</a><a id="8325" class="Symbol">)</a> <a id="8327" class="Symbol">(</a><a id="8328" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8332" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8332" class="Bound">p</a><a id="8333" class="Symbol">)</a> <a id="8335" class="Symbol">(</a><a id="8336" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="8340" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8340" class="Bound">m≤n</a><a id="8343" class="Symbol">)</a> <a id="8345" class="Symbol">(</a><a id="8346" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="8350" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8350" class="Bound">n≤p</a><a id="8353" class="Symbol">)</a> <a id="8355" class="Symbol">=</a> <a id="8357" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="8361" class="Symbol">(</a><a id="8362" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8223" class="Function">≤-trans′</a> <a id="8371" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8316" class="Bound">m</a> <a id="8373" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8324" class="Bound">n</a> <a id="8375" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8332" class="Bound">p</a> <a id="8377" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8340" class="Bound">m≤n</a> <a id="8381" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8350" class="Bound">n≤p</a><a id="8384" class="Symbol">)</a>{% endraw %}</pre>
One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.

The technique of inducting on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on the
value of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.

Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `^C ^C`, `^C ^,`, and `^C ^R` commands.


## Anti-symmetry

The third property to prove about comparison is that it is antisymmetric:
for all naturals `m` and `n`, if both `m ≤ n` and `n ≤ m` hold, then
`m ≡ n` holds.
<pre class="Agda">{% raw %}<a id="≤-antisym"></a><a id="9142" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9142" class="Function">≤-antisym</a> <a id="9152" class="Symbol">:</a> <a id="9154" class="Symbol">∀</a> <a id="9156" class="Symbol">{</a><a id="9157" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9157" class="Bound">m</a> <a id="9159" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9159" class="Bound">n</a> <a id="9161" class="Symbol">:</a> <a id="9163" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="9164" class="Symbol">}</a> <a id="9166" class="Symbol">→</a> <a id="9168" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9157" class="Bound">m</a> <a id="9170" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="9172" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9159" class="Bound">n</a> <a id="9174" class="Symbol">→</a> <a id="9176" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9159" class="Bound">n</a> <a id="9178" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="9180" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9157" class="Bound">m</a> <a id="9182" class="Symbol">→</a> <a id="9184" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9157" class="Bound">m</a> <a id="9186" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="9188" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9159" class="Bound">n</a>
<a id="9190" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9142" class="Function">≤-antisym</a> <a id="9200" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a> <a id="9204" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a> <a id="9208" class="Symbol">=</a> <a id="9210" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="9215" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9142" class="Function">≤-antisym</a> <a id="9225" class="Symbol">(</a><a id="9226" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="9230" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9230" class="Bound">m≤n</a><a id="9233" class="Symbol">)</a> <a id="9235" class="Symbol">(</a><a id="9236" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="9240" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9240" class="Bound">n≤m</a><a id="9243" class="Symbol">)</a> <a id="9245" class="Symbol">=</a> <a id="9247" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#981" class="Function">cong</a> <a id="9252" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9256" class="Symbol">(</a><a id="9257" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9142" class="Function">≤-antisym</a> <a id="9267" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9230" class="Bound">m≤n</a> <a id="9271" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9240" class="Bound">n≤m</a><a id="9274" class="Symbol">)</a>{% endraw %}</pre>
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold, and so we have left `m` and `n` implicit.

In the base case, both inequalities hold by `z≤n`,
and so we are given `zero ≤ zero` and `zero ≤ zero` and must
show `zero ≡ zero`, which follows by reflexivity.  (Reflexivity
of equality, that is, not reflexivity of inequality.)

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality holds by `s≤s n≤m`, and so we are
given `suc m ≤ suc n` and `suc n ≤ suc m` and must show `suc m ≡ suc n`.
The inductive hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`,
and our goal follows by congruence.


## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total.
<pre class="Agda">{% raw %}<a id="10182" class="Keyword">data</a> <a id="Total"></a><a id="10187" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10187" class="Datatype">Total</a> <a id="10193" class="Symbol">(</a><a id="10194" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10194" class="Bound">m</a> <a id="10196" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10196" class="Bound">n</a> <a id="10198" class="Symbol">:</a> <a id="10200" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10201" class="Symbol">)</a> <a id="10203" class="Symbol">:</a> <a id="10205" class="PrimitiveType">Set</a> <a id="10209" class="Keyword">where</a>
  <a id="Total.forward"></a><a id="10217" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10217" class="InductiveConstructor">forward</a> <a id="10225" class="Symbol">:</a> <a id="10227" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10194" class="Bound">m</a> <a id="10229" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="10231" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10196" class="Bound">n</a> <a id="10233" class="Symbol">→</a> <a id="10235" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10187" class="Datatype">Total</a> <a id="10241" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10194" class="Bound">m</a> <a id="10243" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10196" class="Bound">n</a>
  <a id="Total.flipped"></a><a id="10247" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10247" class="InductiveConstructor">flipped</a> <a id="10255" class="Symbol">:</a> <a id="10257" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10196" class="Bound">n</a> <a id="10259" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="10261" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10194" class="Bound">m</a> <a id="10263" class="Symbol">→</a> <a id="10265" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10187" class="Datatype">Total</a> <a id="10271" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10194" class="Bound">m</a> <a id="10273" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10196" class="Bound">n</a>{% endraw %}</pre>
Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

This is our first use of a datatype with *parameters*,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype.
<pre class="Agda">{% raw %}<a id="10592" class="Keyword">data</a> <a id="Total′"></a><a id="10597" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10597" class="Datatype">Total′</a> <a id="10604" class="Symbol">:</a> <a id="10606" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="10608" class="Symbol">→</a> <a id="10610" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="10612" class="Symbol">→</a> <a id="10614" class="PrimitiveType">Set</a> <a id="10618" class="Keyword">where</a>
  <a id="Total′.forward′"></a><a id="10626" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10626" class="InductiveConstructor">forward′</a> <a id="10635" class="Symbol">:</a> <a id="10637" class="Symbol">∀</a> <a id="10639" class="Symbol">{</a><a id="10640" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10640" class="Bound">m</a> <a id="10642" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10642" class="Bound">n</a> <a id="10644" class="Symbol">:</a> <a id="10646" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10647" class="Symbol">}</a> <a id="10649" class="Symbol">→</a> <a id="10651" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10640" class="Bound">m</a> <a id="10653" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="10655" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10642" class="Bound">n</a> <a id="10657" class="Symbol">→</a> <a id="10659" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10597" class="Datatype">Total′</a> <a id="10666" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10640" class="Bound">m</a> <a id="10668" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10642" class="Bound">n</a>
  <a id="Total′.flipped′"></a><a id="10672" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10672" class="InductiveConstructor">flipped′</a> <a id="10681" class="Symbol">:</a> <a id="10683" class="Symbol">∀</a> <a id="10685" class="Symbol">{</a><a id="10686" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10686" class="Bound">m</a> <a id="10688" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10688" class="Bound">n</a> <a id="10690" class="Symbol">:</a> <a id="10692" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10693" class="Symbol">}</a> <a id="10695" class="Symbol">→</a> <a id="10697" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10688" class="Bound">n</a> <a id="10699" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="10701" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10686" class="Bound">m</a> <a id="10703" class="Symbol">→</a> <a id="10705" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10597" class="Datatype">Total′</a> <a id="10712" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10686" class="Bound">m</a> <a id="10714" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10688" class="Bound">n</a>{% endraw %}</pre>
Each parameter of the type translates as an implicit
parameter of each constructor.
Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised
datatype the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and let Agda
exploit the uniformity of the parameters, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality.
<pre class="Agda">{% raw %}<a id="≤-total"></a><a id="11254" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11254" class="Function">≤-total</a> <a id="11262" class="Symbol">:</a> <a id="11264" class="Symbol">∀</a> <a id="11266" class="Symbol">(</a><a id="11267" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11267" class="Bound">m</a> <a id="11269" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11269" class="Bound">n</a> <a id="11271" class="Symbol">:</a> <a id="11273" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="11274" class="Symbol">)</a> <a id="11276" class="Symbol">→</a> <a id="11278" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10187" class="Datatype">Total</a> <a id="11284" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11267" class="Bound">m</a> <a id="11286" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11269" class="Bound">n</a>
<a id="11288" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11254" class="Function">≤-total</a> <a id="11296" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="11304" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11304" class="Bound">n</a>                         <a id="11330" class="Symbol">=</a>  <a id="11333" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10217" class="InductiveConstructor">forward</a> <a id="11341" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a>
<a id="11345" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11254" class="Function">≤-total</a> <a id="11353" class="Symbol">(</a><a id="11354" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11358" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11358" class="Bound">m</a><a id="11359" class="Symbol">)</a> <a id="11361" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="11387" class="Symbol">=</a>  <a id="11390" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10247" class="InductiveConstructor">flipped</a> <a id="11398" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a>
<a id="11402" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11254" class="Function">≤-total</a> <a id="11410" class="Symbol">(</a><a id="11411" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11415" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11415" class="Bound">m</a><a id="11416" class="Symbol">)</a> <a id="11418" class="Symbol">(</a><a id="11419" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11423" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11423" class="Bound">n</a><a id="11424" class="Symbol">)</a> <a id="11426" class="Keyword">with</a> <a id="11431" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11254" class="Function">≤-total</a> <a id="11439" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11415" class="Bound">m</a> <a id="11441" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11423" class="Bound">n</a>
<a id="11443" class="Symbol">...</a>                        <a id="11470" class="Symbol">|</a> <a id="11472" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10217" class="InductiveConstructor">forward</a> <a id="11480" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11480" class="Bound">m≤n</a>  <a id="11485" class="Symbol">=</a>  <a id="11488" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10217" class="InductiveConstructor">forward</a> <a id="11496" class="Symbol">(</a><a id="11497" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="11501" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11480" class="Bound">m≤n</a><a id="11504" class="Symbol">)</a>
<a id="11506" class="Symbol">...</a>                        <a id="11533" class="Symbol">|</a> <a id="11535" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10247" class="InductiveConstructor">flipped</a> <a id="11543" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11543" class="Bound">n≤m</a>  <a id="11548" class="Symbol">=</a>  <a id="11551" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10247" class="InductiveConstructor">flipped</a> <a id="11559" class="Symbol">(</a><a id="11560" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="11564" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11543" class="Bound">n≤m</a><a id="11567" class="Symbol">)</a>{% endraw %}</pre>
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

+ *First base case*: If the first argument is `zero` and the
  second argument is `n` then the forward case holds, 
  with `z≤n` as evidence that `zero ≤ n`.

+ *Second base case*: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

+ *Inductive case*: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  - The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  - The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.

This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.

Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following.
<pre class="Agda">{% raw %}<a id="≤-total′"></a><a id="13076" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13076" class="Function">≤-total′</a> <a id="13085" class="Symbol">:</a> <a id="13087" class="Symbol">∀</a> <a id="13089" class="Symbol">(</a><a id="13090" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13090" class="Bound">m</a> <a id="13092" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13092" class="Bound">n</a> <a id="13094" class="Symbol">:</a> <a id="13096" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="13097" class="Symbol">)</a> <a id="13099" class="Symbol">→</a> <a id="13101" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10187" class="Datatype">Total</a> <a id="13107" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13090" class="Bound">m</a> <a id="13109" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13092" class="Bound">n</a>
<a id="13111" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13076" class="Function">≤-total′</a> <a id="13120" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="13128" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13128" class="Bound">n</a>        <a id="13137" class="Symbol">=</a>  <a id="13140" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10217" class="InductiveConstructor">forward</a> <a id="13148" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a>
<a id="13152" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13076" class="Function">≤-total′</a> <a id="13161" class="Symbol">(</a><a id="13162" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13166" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13166" class="Bound">m</a><a id="13167" class="Symbol">)</a> <a id="13169" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>     <a id="13178" class="Symbol">=</a>  <a id="13181" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10247" class="InductiveConstructor">flipped</a> <a id="13189" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a>
<a id="13193" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13076" class="Function">≤-total′</a> <a id="13202" class="Symbol">(</a><a id="13203" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13207" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13207" class="Bound">m</a><a id="13208" class="Symbol">)</a> <a id="13210" class="Symbol">(</a><a id="13211" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13215" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13215" class="Bound">n</a><a id="13216" class="Symbol">)</a>  <a id="13219" class="Symbol">=</a>  <a id="13222" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13254" class="Function">helper</a> <a id="13229" class="Symbol">(</a><a id="13230" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13076" class="Function">≤-total′</a> <a id="13239" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13207" class="Bound">m</a> <a id="13241" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13215" class="Bound">n</a><a id="13242" class="Symbol">)</a>
  <a id="13246" class="Keyword">where</a>
  <a id="13254" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13254" class="Function">helper</a> <a id="13261" class="Symbol">:</a> <a id="13263" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10187" class="Datatype">Total</a> <a id="13269" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13207" class="Bound">m</a> <a id="13271" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13215" class="Bound">n</a> <a id="13273" class="Symbol">→</a> <a id="13275" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10187" class="Datatype">Total</a> <a id="13281" class="Symbol">(</a><a id="13282" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13286" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13207" class="Bound">m</a><a id="13287" class="Symbol">)</a> <a id="13289" class="Symbol">(</a><a id="13290" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13294" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13215" class="Bound">n</a><a id="13295" class="Symbol">)</a>
  <a id="13299" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13254" class="Function">helper</a> <a id="13306" class="Symbol">(</a><a id="13307" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10217" class="InductiveConstructor">forward</a> <a id="13315" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13315" class="Bound">m≤n</a><a id="13318" class="Symbol">)</a>  <a id="13321" class="Symbol">=</a>  <a id="13324" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10217" class="InductiveConstructor">forward</a> <a id="13332" class="Symbol">(</a><a id="13333" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="13337" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13315" class="Bound">m≤n</a><a id="13340" class="Symbol">)</a>
  <a id="13344" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13254" class="Function">helper</a> <a id="13351" class="Symbol">(</a><a id="13352" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10247" class="InductiveConstructor">flipped</a> <a id="13360" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13360" class="Bound">n≤m</a><a id="13363" class="Symbol">)</a>  <a id="13366" class="Symbol">=</a>  <a id="13369" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10247" class="InductiveConstructor">flipped</a> <a id="13377" class="Symbol">(</a><a id="13378" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="13382" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13360" class="Bound">n≤m</a><a id="13385" class="Symbol">)</a>{% endraw %}</pre>
This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound of the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case.
<pre class="Agda">{% raw %}<a id="≤-total″"></a><a id="14023" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14023" class="Function">≤-total″</a> <a id="14032" class="Symbol">:</a> <a id="14034" class="Symbol">∀</a> <a id="14036" class="Symbol">(</a><a id="14037" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14037" class="Bound">m</a> <a id="14039" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14039" class="Bound">n</a> <a id="14041" class="Symbol">:</a> <a id="14043" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="14044" class="Symbol">)</a> <a id="14046" class="Symbol">→</a> <a id="14048" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10187" class="Datatype">Total</a> <a id="14054" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14037" class="Bound">m</a> <a id="14056" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14039" class="Bound">n</a>
<a id="14058" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14023" class="Function">≤-total″</a> <a id="14067" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14067" class="Bound">m</a>       <a id="14075" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="14101" class="Symbol">=</a>  <a id="14104" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10247" class="InductiveConstructor">flipped</a> <a id="14112" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a>
<a id="14116" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14023" class="Function">≤-total″</a> <a id="14125" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="14133" class="Symbol">(</a><a id="14134" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14138" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14138" class="Bound">n</a><a id="14139" class="Symbol">)</a>                   <a id="14159" class="Symbol">=</a>  <a id="14162" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10217" class="InductiveConstructor">forward</a> <a id="14170" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a>
<a id="14174" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14023" class="Function">≤-total″</a> <a id="14183" class="Symbol">(</a><a id="14184" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14188" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14188" class="Bound">m</a><a id="14189" class="Symbol">)</a> <a id="14191" class="Symbol">(</a><a id="14192" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14196" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14196" class="Bound">n</a><a id="14197" class="Symbol">)</a> <a id="14199" class="Keyword">with</a> <a id="14204" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14023" class="Function">≤-total″</a> <a id="14213" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14188" class="Bound">m</a> <a id="14215" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14196" class="Bound">n</a>
<a id="14217" class="Symbol">...</a>                        <a id="14244" class="Symbol">|</a> <a id="14246" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10217" class="InductiveConstructor">forward</a> <a id="14254" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14254" class="Bound">m≤n</a>   <a id="14260" class="Symbol">=</a>  <a id="14263" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10217" class="InductiveConstructor">forward</a> <a id="14271" class="Symbol">(</a><a id="14272" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="14276" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14254" class="Bound">m≤n</a><a id="14279" class="Symbol">)</a>
<a id="14281" class="Symbol">...</a>                        <a id="14308" class="Symbol">|</a> <a id="14310" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10247" class="InductiveConstructor">flipped</a> <a id="14318" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14318" class="Bound">n≤m</a>   <a id="14324" class="Symbol">=</a>  <a id="14327" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10247" class="InductiveConstructor">flipped</a> <a id="14335" class="Symbol">(</a><a id="14336" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="14340" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14318" class="Bound">n≤m</a><a id="14343" class="Symbol">)</a>{% endraw %}</pre>
It differs from the original code in that it pattern
matches on the second argument before the first argument.


## Monotonicity

If one bumps into both an operator and an ordering at a party, one may ask if
the operator is *monotonic* with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning

  ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right.
<pre class="Agda">{% raw %}<a id="+-monoʳ-≤"></a><a id="14945" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14945" class="Function">+-monoʳ-≤</a> <a id="14955" class="Symbol">:</a> <a id="14957" class="Symbol">∀</a> <a id="14959" class="Symbol">(</a><a id="14960" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14960" class="Bound">m</a> <a id="14962" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14962" class="Bound">p</a> <a id="14964" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14964" class="Bound">q</a> <a id="14966" class="Symbol">:</a> <a id="14968" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="14969" class="Symbol">)</a> <a id="14971" class="Symbol">→</a> <a id="14973" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14962" class="Bound">p</a> <a id="14975" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="14977" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14964" class="Bound">q</a> <a id="14979" class="Symbol">→</a> <a id="14981" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14960" class="Bound">m</a> <a id="14983" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14985" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14962" class="Bound">p</a> <a id="14987" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="14989" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14960" class="Bound">m</a> <a id="14991" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14993" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14964" class="Bound">q</a>
<a id="14995" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14945" class="Function">+-monoʳ-≤</a> <a id="15005" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="15013" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15013" class="Bound">p</a> <a id="15015" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15015" class="Bound">q</a> <a id="15017" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15017" class="Bound">p≤q</a>  <a id="15022" class="Symbol">=</a>  <a id="15025" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15017" class="Bound">p≤q</a>
<a id="15029" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14945" class="Function">+-monoʳ-≤</a> <a id="15039" class="Symbol">(</a><a id="15040" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15044" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15044" class="Bound">m</a><a id="15045" class="Symbol">)</a> <a id="15047" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15047" class="Bound">p</a> <a id="15049" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15049" class="Bound">q</a> <a id="15051" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15051" class="Bound">p≤q</a>  <a id="15056" class="Symbol">=</a>  <a id="15059" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="15063" class="Symbol">(</a><a id="15064" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14945" class="Function">+-monoʳ-≤</a> <a id="15074" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15044" class="Bound">m</a> <a id="15076" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15047" class="Bound">p</a> <a id="15078" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15049" class="Bound">q</a> <a id="15080" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15051" class="Bound">p≤q</a><a id="15083" class="Symbol">)</a>{% endraw %}</pre>
The proof is by induction on the first argument.

+ *Base case*: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

+ *Inductive case*: The first argument is `suc m`, in which case
  `suc m + p ≤ suc m + q` simplifies to `suc (m + p) ≤ suc (m + q)`.
  The inductive hypothesis `+-monoʳ-≤ m p q p≤q` establishes that
  `m + p ≤ m + q`, and our goal follows by applying `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition.
<pre class="Agda">{% raw %}<a id="+-monoˡ-≤"></a><a id="15740" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15740" class="Function">+-monoˡ-≤</a> <a id="15750" class="Symbol">:</a> <a id="15752" class="Symbol">∀</a> <a id="15754" class="Symbol">(</a><a id="15755" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15755" class="Bound">m</a> <a id="15757" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15757" class="Bound">n</a> <a id="15759" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15759" class="Bound">p</a> <a id="15761" class="Symbol">:</a> <a id="15763" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="15764" class="Symbol">)</a> <a id="15766" class="Symbol">→</a> <a id="15768" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15755" class="Bound">m</a> <a id="15770" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="15772" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15757" class="Bound">n</a> <a id="15774" class="Symbol">→</a> <a id="15776" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15755" class="Bound">m</a> <a id="15778" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15780" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15759" class="Bound">p</a> <a id="15782" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="15784" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15757" class="Bound">n</a> <a id="15786" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15788" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15759" class="Bound">p</a>
<a id="15790" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15740" class="Function">+-monoˡ-≤</a> <a id="15800" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15800" class="Bound">m</a> <a id="15802" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15802" class="Bound">n</a> <a id="15804" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15804" class="Bound">p</a> <a id="15806" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15806" class="Bound">m≤n</a> <a id="15810" class="Keyword">rewrite</a> <a id="15818" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8101" class="Function">+-comm</a> <a id="15825" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15800" class="Bound">m</a> <a id="15827" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15804" class="Bound">p</a> <a id="15829" class="Symbol">|</a> <a id="15831" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8101" class="Function">+-comm</a> <a id="15838" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15802" class="Bound">n</a> <a id="15840" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15804" class="Bound">p</a> <a id="15842" class="Symbol">=</a> <a id="15844" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14945" class="Function">+-monoʳ-≤</a> <a id="15854" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15804" class="Bound">p</a> <a id="15856" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15800" class="Bound">m</a> <a id="15858" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15802" class="Bound">n</a> <a id="15860" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15806" class="Bound">m≤n</a>{% endraw %}</pre>
Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results.
<pre class="Agda">{% raw %}<a id="+-mono-≤"></a><a id="16074" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16074" class="Function">+-mono-≤</a> <a id="16083" class="Symbol">:</a> <a id="16085" class="Symbol">∀</a> <a id="16087" class="Symbol">(</a><a id="16088" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16088" class="Bound">m</a> <a id="16090" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16090" class="Bound">n</a> <a id="16092" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16092" class="Bound">p</a> <a id="16094" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16094" class="Bound">q</a> <a id="16096" class="Symbol">:</a> <a id="16098" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16099" class="Symbol">)</a> <a id="16101" class="Symbol">→</a> <a id="16103" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16088" class="Bound">m</a> <a id="16105" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="16107" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16090" class="Bound">n</a> <a id="16109" class="Symbol">→</a> <a id="16111" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16092" class="Bound">p</a> <a id="16113" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="16115" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16094" class="Bound">q</a> <a id="16117" class="Symbol">→</a> <a id="16119" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16088" class="Bound">m</a> <a id="16121" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16123" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16092" class="Bound">p</a> <a id="16125" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="16127" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16090" class="Bound">n</a> <a id="16129" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16131" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16094" class="Bound">q</a>
<a id="16133" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16074" class="Function">+-mono-≤</a> <a id="16142" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16142" class="Bound">m</a> <a id="16144" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16144" class="Bound">n</a> <a id="16146" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16146" class="Bound">p</a> <a id="16148" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16148" class="Bound">q</a> <a id="16150" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16150" class="Bound">m≤n</a> <a id="16154" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16154" class="Bound">p≤q</a> <a id="16158" class="Symbol">=</a> <a id="16160" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6281" class="Function">≤-trans</a> <a id="16168" class="Symbol">(</a><a id="16169" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15740" class="Function">+-monoˡ-≤</a> <a id="16179" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16142" class="Bound">m</a> <a id="16181" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16144" class="Bound">n</a> <a id="16183" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16146" class="Bound">p</a> <a id="16185" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16150" class="Bound">m≤n</a><a id="16188" class="Symbol">)</a> <a id="16190" class="Symbol">(</a><a id="16191" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14945" class="Function">+-monoʳ-≤</a> <a id="16201" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16144" class="Bound">n</a> <a id="16203" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16146" class="Bound">p</a> <a id="16205" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16148" class="Bound">q</a> <a id="16207" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16154" class="Bound">p≤q</a><a id="16210" class="Symbol">)</a>{% endraw %}</pre>
Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


## Strict inequality.

We can define strict inequality similarly to inequality.
<pre class="Agda">{% raw %}<a id="16513" class="Keyword">infix</a> <a id="16519" class="Number">4</a> <a id="16521" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16531" class="Datatype Operator">_&lt;_</a>

<a id="16526" class="Keyword">data</a> <a id="_&lt;_"></a><a id="16531" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16531" class="Datatype Operator">_&lt;_</a> <a id="16535" class="Symbol">:</a> <a id="16537" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="16539" class="Symbol">→</a> <a id="16541" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="16543" class="Symbol">→</a> <a id="16545" class="PrimitiveType">Set</a> <a id="16549" class="Keyword">where</a>
  <a id="_&lt;_.z&lt;s"></a><a id="16557" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16557" class="InductiveConstructor">z&lt;s</a> <a id="16561" class="Symbol">:</a> <a id="16563" class="Symbol">∀</a> <a id="16565" class="Symbol">{</a><a id="16566" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16566" class="Bound">n</a> <a id="16568" class="Symbol">:</a> <a id="16570" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16571" class="Symbol">}</a> <a id="16573" class="Symbol">→</a> <a id="16575" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="16580" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16531" class="Datatype Operator">&lt;</a> <a id="16582" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16586" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16566" class="Bound">n</a>
  <a id="_&lt;_.s&lt;s"></a><a id="16590" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16590" class="InductiveConstructor">s&lt;s</a> <a id="16594" class="Symbol">:</a> <a id="16596" class="Symbol">∀</a> <a id="16598" class="Symbol">{</a><a id="16599" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16599" class="Bound">m</a> <a id="16601" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16601" class="Bound">n</a> <a id="16603" class="Symbol">:</a> <a id="16605" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16606" class="Symbol">}</a> <a id="16608" class="Symbol">→</a> <a id="16610" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16599" class="Bound">m</a> <a id="16612" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16531" class="Datatype Operator">&lt;</a> <a id="16614" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16601" class="Bound">n</a> <a id="16616" class="Symbol">→</a> <a id="16618" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16622" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16599" class="Bound">m</a> <a id="16624" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16531" class="Datatype Operator">&lt;</a> <a id="16626" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16630" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16601" class="Bound">n</a>{% endraw %}</pre>
The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.

Clearly, strict inequality is not reflexive. However it is
*irreflexive* in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
*trichotomy*: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly where `n < m`).
It is also monotonic with regards to addition and multiplication.

Most of the above are considered in exercises below.  Irreflexivity
requires logical negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred
until the negation is introduced in Chapter [Logic](Logic).

It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by directly
exploiting the corresponding properties of inequality.

### Exercise (`<-trans`)

Show that strict inequality is transitive.

### Exercise (`trichotomy`)

Show that strict inequality satisfies a weak version of trichotomy, in the sense
that for any `m` and `n` that one of `m < n`, `m ≡ n`, or `m > n`
holds. You will need to define a suitable data structure, similar
to the one used for totality.  (After negation is introduced in Chapter [Logic](Logic),
we will be in a position to show that the three cases are mutually exclusive.)

### Exercise (`+-mono-<`)

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

### Exercise (`≤-implies-<`, `<-implies-≤`)

Show that `suc m ≤ n` implies `m < n`, and conversely.

### Exercise (`<-trans′`)

Give an alternative proof that strict inequality is transitive,
using the relating between strict inequality and inequality and
the fact that inequality is transitive.


## Even and odd

As a further example, let's specify even and odd numbers.  
Inequality and strict inequality are *binary relations*,
while even and odd are *unary relations*, sometimes called *predicates*.
<pre class="Agda">{% raw %}<a id="18888" class="Keyword">data</a> <a id="even"></a><a id="18893" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18893" class="Datatype">even</a> <a id="18898" class="Symbol">:</a> <a id="18900" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="18902" class="Symbol">→</a> <a id="18904" class="PrimitiveType">Set</a>
<a id="18908" class="Keyword">data</a> <a id="odd"></a><a id="18913" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18913" class="Datatype">odd</a>  <a id="18918" class="Symbol">:</a> <a id="18920" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="18922" class="Symbol">→</a> <a id="18924" class="PrimitiveType">Set</a>

<a id="18929" class="Keyword">data</a> <a id="18934" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18893" class="Datatype">even</a> <a id="18939" class="Keyword">where</a>
  <a id="even.even-zero"></a><a id="18947" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18947" class="InductiveConstructor">even-zero</a> <a id="18957" class="Symbol">:</a> <a id="18959" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18893" class="Datatype">even</a> <a id="18964" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="even.even-suc"></a><a id="18971" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18971" class="InductiveConstructor">even-suc</a>  <a id="18981" class="Symbol">:</a> <a id="18983" class="Symbol">∀</a> <a id="18985" class="Symbol">{</a><a id="18986" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18986" class="Bound">n</a> <a id="18988" class="Symbol">:</a> <a id="18990" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="18991" class="Symbol">}</a> <a id="18993" class="Symbol">→</a> <a id="18995" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18913" class="Datatype">odd</a> <a id="18999" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18986" class="Bound">n</a> <a id="19001" class="Symbol">→</a> <a id="19003" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18893" class="Datatype">even</a> <a id="19008" class="Symbol">(</a><a id="19009" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="19013" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18986" class="Bound">n</a><a id="19014" class="Symbol">)</a>

<a id="19017" class="Keyword">data</a> <a id="19022" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18913" class="Datatype">odd</a> <a id="19026" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="19034" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19034" class="InductiveConstructor">odd-suc</a>   <a id="19044" class="Symbol">:</a> <a id="19046" class="Symbol">∀</a> <a id="19048" class="Symbol">{</a><a id="19049" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19049" class="Bound">n</a> <a id="19051" class="Symbol">:</a> <a id="19053" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="19054" class="Symbol">}</a> <a id="19056" class="Symbol">→</a> <a id="19058" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18893" class="Datatype">even</a> <a id="19063" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19049" class="Bound">n</a> <a id="19065" class="Symbol">→</a> <a id="19067" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18913" class="Datatype">odd</a> <a id="19071" class="Symbol">(</a><a id="19072" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="19076" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19049" class="Bound">n</a><a id="19077" class="Symbol">)</a>{% endraw %}</pre>
A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.

This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).

We show that the sum of two even numbers is even.
<pre class="Agda">{% raw %}<a id="e+e≡e"></a><a id="19616" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19616" class="Function">e+e≡e</a> <a id="19622" class="Symbol">:</a> <a id="19624" class="Symbol">∀</a> <a id="19626" class="Symbol">{</a><a id="19627" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19627" class="Bound">m</a> <a id="19629" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19629" class="Bound">n</a> <a id="19631" class="Symbol">:</a> <a id="19633" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="19634" class="Symbol">}</a> <a id="19636" class="Symbol">→</a> <a id="19638" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18893" class="Datatype">even</a> <a id="19643" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19627" class="Bound">m</a> <a id="19645" class="Symbol">→</a> <a id="19647" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18893" class="Datatype">even</a> <a id="19652" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19629" class="Bound">n</a> <a id="19654" class="Symbol">→</a> <a id="19656" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18893" class="Datatype">even</a> <a id="19661" class="Symbol">(</a><a id="19662" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19627" class="Bound">m</a> <a id="19664" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="19666" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19629" class="Bound">n</a><a id="19667" class="Symbol">)</a>
<a id="o+e≡o"></a><a id="19669" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19669" class="Function">o+e≡o</a> <a id="19675" class="Symbol">:</a> <a id="19677" class="Symbol">∀</a> <a id="19679" class="Symbol">{</a><a id="19680" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19680" class="Bound">m</a> <a id="19682" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19682" class="Bound">n</a> <a id="19684" class="Symbol">:</a> <a id="19686" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="19687" class="Symbol">}</a> <a id="19689" class="Symbol">→</a> <a id="19691" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18913" class="Datatype">odd</a>  <a id="19696" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19680" class="Bound">m</a> <a id="19698" class="Symbol">→</a> <a id="19700" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18893" class="Datatype">even</a> <a id="19705" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19682" class="Bound">n</a> <a id="19707" class="Symbol">→</a> <a id="19709" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18913" class="Datatype">odd</a>  <a id="19714" class="Symbol">(</a><a id="19715" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19680" class="Bound">m</a> <a id="19717" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="19719" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19682" class="Bound">n</a><a id="19720" class="Symbol">)</a>

<a id="19723" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19616" class="Function">e+e≡e</a> <a id="19729" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18947" class="InductiveConstructor">even-zero</a>     <a id="19743" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19743" class="Bound">en</a>  <a id="19747" class="Symbol">=</a>  <a id="19750" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19743" class="Bound">en</a>
<a id="19753" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19616" class="Function">e+e≡e</a> <a id="19759" class="Symbol">(</a><a id="19760" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18971" class="InductiveConstructor">even-suc</a> <a id="19769" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19769" class="Bound">om</a><a id="19771" class="Symbol">)</a> <a id="19773" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19773" class="Bound">en</a>  <a id="19777" class="Symbol">=</a>  <a id="19780" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18971" class="InductiveConstructor">even-suc</a> <a id="19789" class="Symbol">(</a><a id="19790" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19669" class="Function">o+e≡o</a> <a id="19796" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19769" class="Bound">om</a> <a id="19799" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19773" class="Bound">en</a><a id="19801" class="Symbol">)</a>

<a id="19804" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19669" class="Function">o+e≡o</a> <a id="19810" class="Symbol">(</a><a id="19811" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19034" class="InductiveConstructor">odd-suc</a>  <a id="19820" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19820" class="Bound">em</a><a id="19822" class="Symbol">)</a> <a id="19824" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19824" class="Bound">en</a>  <a id="19828" class="Symbol">=</a>  <a id="19831" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19034" class="InductiveConstructor">odd-suc</a>  <a id="19840" class="Symbol">(</a><a id="19841" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19616" class="Function">e+e≡e</a> <a id="19847" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19820" class="Bound">em</a> <a id="19850" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19824" class="Bound">en</a><a id="19852" class="Symbol">)</a>{% endraw %}</pre>
Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.

To show that the sum of two even numbers is even, consider the evidence that the
first number is even. If it because it is zero, then the sum is even because the
second number is even.  If it is because it is the successor of an odd number,
then the result is even because it is the successor of the sum of an odd and an
even number, which is odd.

To show that the sum of an odd and even number is odd, consider the evidence
that the first number is odd. If it is because it is the successor of an even
number, then the result is odd because it is the successor of the sum of two
even numbers, which is even.

This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.

### Exercise (`o+o≡e`)

Show that the sum of two odd numbers is even.


## Formalising preorder

<pre class="Agda">{% raw %}<a id="21004" class="Keyword">record</a> <a id="IsPreorder"></a><a id="21011" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21011" class="Record">IsPreorder</a> <a id="21022" class="Symbol">{</a><a id="21023" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21023" class="Bound">A</a> <a id="21025" class="Symbol">:</a> <a id="21027" class="PrimitiveType">Set</a><a id="21030" class="Symbol">}</a> <a id="21032" class="Symbol">(</a><a id="21033" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21033" class="Bound Operator">_≤_</a> <a id="21037" class="Symbol">:</a> <a id="21039" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21023" class="Bound">A</a> <a id="21041" class="Symbol">→</a> <a id="21043" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21023" class="Bound">A</a> <a id="21045" class="Symbol">→</a> <a id="21047" class="PrimitiveType">Set</a><a id="21050" class="Symbol">)</a> <a id="21052" class="Symbol">:</a> <a id="21054" class="PrimitiveType">Set</a> <a id="21058" class="Keyword">where</a>
  <a id="21066" class="Keyword">field</a>
    <a id="IsPreorder.reflexive"></a><a id="21076" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21076" class="Field">reflexive</a> <a id="21086" class="Symbol">:</a> <a id="21088" class="Symbol">∀</a> <a id="21090" class="Symbol">{</a><a id="21091" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21091" class="Bound">x</a> <a id="21093" class="Symbol">:</a> <a id="21095" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21023" class="Bound">A</a><a id="21096" class="Symbol">}</a> <a id="21098" class="Symbol">→</a> <a id="21100" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21091" class="Bound">x</a> <a id="21102" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21033" class="Bound Operator">≤</a> <a id="21104" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21091" class="Bound">x</a>
    <a id="IsPreorder.trans"></a><a id="21110" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21110" class="Field">trans</a> <a id="21116" class="Symbol">:</a> <a id="21118" class="Symbol">∀</a> <a id="21120" class="Symbol">{</a><a id="21121" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21121" class="Bound">x</a> <a id="21123" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21123" class="Bound">y</a> <a id="21125" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21125" class="Bound">z</a> <a id="21127" class="Symbol">:</a> <a id="21129" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21023" class="Bound">A</a><a id="21130" class="Symbol">}</a> <a id="21132" class="Symbol">→</a> <a id="21134" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21121" class="Bound">x</a> <a id="21136" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21033" class="Bound Operator">≤</a> <a id="21138" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21123" class="Bound">y</a> <a id="21140" class="Symbol">→</a> <a id="21142" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21123" class="Bound">y</a> <a id="21144" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21033" class="Bound Operator">≤</a> <a id="21146" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21125" class="Bound">z</a> <a id="21148" class="Symbol">→</a> <a id="21150" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21121" class="Bound">x</a> <a id="21152" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21033" class="Bound Operator">≤</a> <a id="21154" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21125" class="Bound">z</a>

<a id="IsPreorder-≤"></a><a id="21157" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21157" class="Function">IsPreorder-≤</a> <a id="21170" class="Symbol">:</a> <a id="21172" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21011" class="Record">IsPreorder</a> <a id="21183" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">_≤_</a>
<a id="21187" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21157" class="Function">IsPreorder-≤</a> <a id="21200" class="Symbol">=</a>
  <a id="21204" class="Keyword">record</a>
    <a id="21215" class="Symbol">{</a> <a id="21217" class="Field">reflexive</a> <a id="21227" class="Symbol">=</a> <a id="21229" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#5623" class="Function">≤-refl</a>
    <a id="21240" class="Symbol">;</a> <a id="21242" class="Field">trans</a> <a id="21248" class="Symbol">=</a> <a id="21250" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6281" class="Function">≤-trans</a>
    <a id="21262" class="Symbol">}</a>{% endraw %}</pre>



## Standard prelude

Definitions similar to those in this chapter can be found in the standard library.
<pre class="Agda">{% raw %}<a id="21395" class="Keyword">import</a> <a id="21402" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="21411" class="Keyword">using</a> <a id="21417" class="Symbol">(</a><a id="21418" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#802" class="Datatype Operator">_≤_</a><a id="21421" class="Symbol">;</a> <a id="21423" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#833" class="InductiveConstructor">z≤n</a><a id="21426" class="Symbol">;</a> <a id="21428" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#875" class="InductiveConstructor">s≤s</a><a id="21431" class="Symbol">)</a>
<a id="21433" class="Keyword">import</a> <a id="21440" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="21460" class="Keyword">using</a> <a id="21466" class="Symbol">(</a><a id="21467" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#1888" class="Function">≤-refl</a><a id="21473" class="Symbol">;</a> <a id="21475" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2081" class="Function">≤-trans</a><a id="21482" class="Symbol">;</a> <a id="21484" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#1938" class="Function">≤-antisym</a><a id="21493" class="Symbol">;</a> <a id="21495" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2193" class="Function">≤-total</a><a id="21502" class="Symbol">;</a>
                                  <a id="21538" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#10972" class="Function">+-monoʳ-≤</a><a id="21547" class="Symbol">;</a> <a id="21549" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#10882" class="Function">+-monoˡ-≤</a><a id="21558" class="Symbol">;</a> <a id="21560" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#10726" class="Function">+-mono-≤</a><a id="21568" class="Symbol">)</a>{% endraw %}</pre>
In the standard library, `≤-total` is formalised in terms of disjunction (which
we define in Chapter [Logic](Logic)), and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤`
make implicit arguments that here are explicit.

## Unicode

This chapter uses the following unicode.

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (̄\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)

The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows, and also superscript letters `l` and `r`.

