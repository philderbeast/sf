---
title     : "Naturals: Natural numbers"
layout    : page
permalink : /Naturals
---

The night sky holds more stars than I can count, though less than five
thousand are visible to the naked sky.  The observable universe
contains about seventy sextillion stars.

But the number of stars is finite, while natural numbers are infinite.
Count all the stars, and you will still have as many natural numbers
left over as you started with.


## The naturals are an inductive datatype

Everyone is familiar with the natural numbers:

    0
    1
    2
    3
    ...

and so on. We write `ℕ` for the *type* of natural numbers, and say that
`0`, `1`, `2`, `3`, and so on are *values* of type `ℕ`, indicated by
writing `0 : ℕ`, `1 : ℕ`, `2 : ℕ`, `3 : ℕ`, and so on.

The set of natural numbers is infinite, yet we can write down
its definition in just a few lines.  Here is the definition
as a pair of inference rules:

    --------
    zero : ℕ

    m : ℕ
    ---------
    suc m : ℕ

And here is the definition in Agda:
<pre class="Agda">{% raw %}<a id="1028" class="Keyword">data</a> <a id="ℕ"></a><a id="1033" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1033" class="Datatype">ℕ</a> <a id="1035" class="Symbol">:</a> <a id="1037" class="PrimitiveType">Set</a> <a id="1041" class="Keyword">where</a>
  <a id="ℕ.zero"></a><a id="1049" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1049" class="InductiveConstructor">zero</a> <a id="1054" class="Symbol">:</a> <a id="1056" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1033" class="Datatype">ℕ</a>
  <a id="ℕ.suc"></a><a id="1060" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a>  <a id="1065" class="Symbol">:</a> <a id="1067" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1033" class="Datatype">ℕ</a> <a id="1069" class="Symbol">→</a> <a id="1071" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1033" class="Datatype">ℕ</a>{% endraw %}</pre>
Here `ℕ` is the name of the *datatype* we are defining,
and `zero` and `suc` (short for *successor*) are the
*constructors* of the datatype.

Both definitions above tell us the same two things:

+ *Base case*: `zero` is a natural number.
+ *Inductive case*: if `m` is a natural number, then `suc m` is also a
  natural number.

Further, these two rules give the *only* ways of creating natural numbers.
Hence, the possible natural numbers are

    zero
    suc zero
    suc (suc zero)
    suc (suc (suc zero))
    ...

We write `0` as shorthand for `zero`; and `1` is shorthand
for `suc zero`, the successor of zero, that is, the natural that comes
after zero; and `2` is shorthand for `suc (suc zero)`, which is the
same as `suc 1`, the successor of one; and `3` is shorthand for the
successor of two; and so on.

### Exercise (`longhand`)

Write out `7` in longhand.


## Unpacking the inference rules

Let's unpack the inference rules.  Each inference rule consists of
zero or more *judgments* written above a horizontal line, called the
*hypotheses*, and a single judgment written below, called the
*conclusion*.  The first rule is the base case. It has no hypotheses,
and the conclusion asserts that `zero` is a natural.  The second rule
is the inductive case. It has one hypothesis, which assumes that `m`
is a natural, and the conclusion asserts that `suc n` is a also a
natural.


## Unpacking the Agda definition

Let's unpack the Agda definition. The keyword `data` tells us this is an
inductive definition, that is, that we are defining a new datatype
with constructors.  The phrase

    ℕ : Set

tells us that `ℕ` is the name of the new datatype, and that it is a
`Set`, which is the way in Agda of saying that it is a type.  The
keyword `where` separates the declaration of the datatype from the
declaration of its constructors. Each constructor is declared on a
separate line, which is indented to indicate that it belongs to the
corresponding `data` declaration.  The lines

    zero : ℕ
    suc : ℕ → ℕ

give *signatures* specifying the types of the constructors `zero` and `suc`.
They tell us that `zero` is a natural number and that `suc` takes a natural
number as argument and returns a natural number.

You may have noticed that `ℕ` and `→` don't appear on your keyboard.
They are symbols in *unicode*.  At the end of each chapter is a list
of all unicode symbols introduced in the chapter, including
instructions on how to type them in the Emacs text editor.  Here
*type* refers to typing with fingers as opposed to data typing!


## The story of creation

Let's look again at the rules that define the natural numbers:

+ *Base case*: `zero` is a natural number.
+ *Inductive case*: if `m` is a natural number, then `suc m` is also a
  natural number.

Hold on! The second line defines natural numbers in terms of natural
numbers. How can that possibly be allowed?  Isn't this as meaningless
as the claim "Brexit means Brexit"?

In fact, it is possible to assign our definition a meaning without
resorting to any unpermitted circularities.  Furthermore, we can do so
while only working with *finite* sets and never referring to the
entire *infinite* set of natural numbers.

We will think of it as a creation story.  To start with, we know about
no natural numbers at all.

    -- in the beginning, there are no natural numbers

Now, we apply the rules to all the natural numbers we know about.  The
base case tells us that `zero` is a natural number, so we add it to the set
of known natural numbers.  The inductive case tells us that if `m` is a
natural number (on the day before today) then `suc m` is also a
natural number (today).  We didn't know about any natural numbers
before today, so the inductive case doesn't apply.

    -- on the first day, there is one natural number   
    zero : ℕ

Then we repeat the process. On the next day we know about all the
numbers from the day before, plus any numbers added by the rules.  The
base case tells us that `zero` is a natural number, but we already knew
that. But now the inductive case tells us that since `zero` was a natural
number yesterday, then `suc zero` is a natural number today.

    -- on the second day, there are two natural numbers
    zero : ℕ
    suc zero : ℕ

And we repeat the process again. Now the inductive case
tells us that since `zero` and `suc zero` are both natural numbers, then
`suc zero` and `suc (suc zero)` are natural numbers. We already knew about
the first of these, but the second is new.

    -- on the third day, there are three natural numbers
    zero : ℕ
    suc zero : ℕ
    suc (suc zero) : ℕ

You've got the hang of it by now.

    -- on the fourth day, there are four natural numbers
    zero : ℕ
    suc zero : ℕ
    suc (suc zero) : ℕ
    suc (suc (suc zero)) : ℕ

The process continues.  On the *n*th day there will be *n* distinct
natural numbers. Every natural number will appear on some given day.
In particular, the number *n* first appears on day *n+1*. And we
never actually define the set of numbers in terms of itself. Instead,
we define the set of numbers on day *n+1* in terms of the set of
numbers on day *n*.

A process like this one is called *inductive*. We start with nothing, and
build up a potentially infinite set by applying rules that convert one
finite set into another finite set.

The rule defining zero is called a *base case*, because it introduces
a natural number even when we know no other natural numbers.  The rule
defining successor is called an *inductive case*, because it
introduces more natural numbers once we already know some.  Note the
crucial role of the base case.  If we only had inductive rules, then
we would have no numbers in the beginning, and still no numbers on the
second day, and on the third, and so on.  An inductive definition lacking
a base case is useless, as in the phrase "Brexit means Brexit".


## Philosophy and history

A philosopher might observe that our reference to the first day,
second day, and so on, implicitly involves an understanding of natural
numbers.  In this sense, our definition might indeed be regarded as in
some sense circular, but we need not let this disturb us.
Everyone possesses a good informal understanding of the natural
numbers, which we may take as a foundation for their formal
description.

While the natural numbers have been understood for as long as people
can count, the inductive definition of the natural numbers is relatively
recent.  It can be traced back to Richard Dedekind's paper "*Was sind
und was sollen die Zahlen?*" (What are and what should be the
numbers?), published in 1888, and Giuseppe Peano's book "*Arithmetices
principia, nova methodo exposita*" (The principles of arithmetic
presented by a new method), published the following year.


## A pragma

In Agda, any text following `--` or enclosed between `{-`
and `-}` is considered a *comment*.  Comments have no effect on the
code, with the exception of one special kind of comment, called a
*pragma*, which is enclosed between `{-#` and `#-}`.

Including the line
<pre class="Agda">{% raw %}<a id="8154" class="Symbol">{-#</a> <a id="8158" class="Keyword">BUILTIN</a> NATURAL <a id="8174" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1033" class="Datatype">ℕ</a> <a id="8176" class="Symbol">#-}</a>{% endraw %}</pre>
tells Agda that `ℕ` corresponds to the natural numbers, and hence one
is permitted to type `0` as shorthand for `zero`, `1` as shorthand for
`suc zero`, `2` as shorthand for `suc (suc zero)`, and so on.  The
declaration is not permitted unless the type given has two constructors,
one corresponding to zero and one to successor.

As well as enabling the above shorthand, the pragma also enables a
more efficient internal representation of naturals using the Haskell
type for arbitrary-precision integers.  Representing the natural *n*
with `zero` and `suc` requires space proportional to *n*, whereas
representing it as an arbitary-precision integer in Haskell only
requires space proportional to the logarithm base 2 of *n*.


## Imports

Shortly we will want to write some equivalences that hold between
terms involving natural numbers.  To support doing so, we import
the definition of equivalence and some notations for reasoning
about it from the Agda standard library.

<pre class="Agda">{% raw %}<a id="9180" class="Keyword">import</a> <a id="9187" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="9225" class="Symbol">as</a> <a id="9228" class="Module">Eq</a>
<a id="9231" class="Keyword">open</a> <a id="9236" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="9239" class="Keyword">using</a> <a id="9245" class="Symbol">(</a><a id="9246" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="9249" class="Symbol">;</a> <a id="9251" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="9255" class="Symbol">)</a>
<a id="9257" class="Keyword">open</a> <a id="9262" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3767" class="Module">Eq.≡-Reasoning</a> <a id="9277" class="Keyword">using</a> <a id="9283" class="Symbol">(</a><a id="9284" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3868" class="Function Operator">begin_</a><a id="9290" class="Symbol">;</a> <a id="9292" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">_≡⟨⟩_</a><a id="9297" class="Symbol">;</a> <a id="9299" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4166" class="Function Operator">_∎</a><a id="9301" class="Symbol">)</a>{% endraw %}</pre>

The first line brings the standard library module that defines
propositional equality into scope, with the name `Eq`. The second line
opens that module, that is, adds all the names specified in the
`using` clause into the current scope. In this case the names added
are `_≡_`, the equivalence operator, and `refl`, the name for evidence
that two terms are equal.  The third line takes a record that
specifies operators to support reasoning about equivalence, and adds
all the names specified in the `using` clause into the current scope.
In this case, the names added are `begin_`, `_≡⟨⟩_`, and `_∎`.  We
will see how these are used below.  We take all these as givens for now,
but will see how they are defined in Chapter [Equivalence](Equivalence).

Agda uses underbars to indicate where terms appear in infix or mixfix
operators. Thus, `_≡_` and `_≡⟨⟩_` are infix (each operator is written
between two terms), while `begin_` is prefix (it is written before a
term), and `_∎` is postfix (it is written after a term).

Parentheses and semicolons are among the few characters that cannot
appear in names, so we do not need extra spaces in the `using` list.


## Operations on naturals are recursive functions

Now that we have the natural numbers, what can we do with them?
For instance, can we define arithmetic operations such as
addition and multiplication?

As a child I spent much time memorising tables of addition and
multiplication.  At first the rules seemed tricky and I would often
make mistakes.  It came as a shock to me to discover *recursion*,
a simple technique by which every one of the infinite possible
instances of addition and multiplication can be specified in
just a couple of lines.

Here is the definition of addition in Agda:
<pre class="Agda">{% raw %}<a id="_+_"></a><a id="11080" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Function Operator">_+_</a> <a id="11084" class="Symbol">:</a> <a id="11086" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1033" class="Datatype">ℕ</a> <a id="11088" class="Symbol">→</a> <a id="11090" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1033" class="Datatype">ℕ</a> <a id="11092" class="Symbol">→</a> <a id="11094" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1033" class="Datatype">ℕ</a>
<a id="11096" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1049" class="InductiveConstructor">zero</a>    <a id="11104" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Function Operator">+</a> <a id="11106" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11106" class="Bound">n</a>  <a id="11109" class="Symbol">=</a>  <a id="11112" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11106" class="Bound">n</a>
<a id="11114" class="Symbol">(</a><a id="11115" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="11119" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11119" class="Bound">m</a><a id="11120" class="Symbol">)</a> <a id="11122" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Function Operator">+</a> <a id="11124" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11124" class="Bound">n</a>  <a id="11127" class="Symbol">=</a>  <a id="11130" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="11134" class="Symbol">(</a><a id="11135" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11119" class="Bound">m</a> <a id="11137" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Function Operator">+</a> <a id="11139" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11124" class="Bound">n</a><a id="11140" class="Symbol">)</a>{% endraw %}</pre>

Let's unpack this definition.  Addition is an infix operator.  It is
written with underbars where the argument go, hence its name is
`_+_`.  The first line is a signature specifying the type of the operator.
The type `ℕ → ℕ → ℕ`, indicates that addition accepts two naturals
and returns a natural.  Infix notation is just a shorthand for application;
the terms `m + n` and `_+_ m n` are equivalent.  

The definition has a base case and an inductive case, corresponding to
those for the natural numbers.  The base case says that adding zero to
a number, `zero + n`, returns that number, `n`.  The inductive case
says that adding the successor of a number to another number,
`(suc m) + n`, returns the successor of adding the two numbers, `suc (m+n)`.
We say we are using *pattern matching* when constructors appear on the
left-hand side of an equation.

If we write `zero` as `0` and `suc m` as `1 + m`, the definition turns
into two familiar equations.

     0       + n  ≡  n
     (1 + m) + n  ≡  1 + (m + n)

The first follows because zero is an identity for addition, and the
second because addition is associative.  In its most general form,
associativity is written

     (m + n) + p  ≡  m + (n + p)

meaning that the order of parentheses is irrelevant.  We get the
second equation from this one by taking `m` to be `1`, `n` to be `m`,
and `p` to be `n`.  We write `=` for definitions, while we
write `≡` for assertions that two already defined things are the same.

The definition is *recursive*, in that the last line defines addition
in terms of addition.  As with the inductive definition of the
naturals, the apparent circularity is not a problem.  It works because
addition of larger numbers is defined in terms of addition of smaller
numbers.  Such a definition is called *well founded*.

For example, let's add two and three.
<pre class="Agda">{% raw %}<a id="13007" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#13007" class="Function">_</a> <a id="13009" class="Symbol">:</a> <a id="13011" class="Number">2</a> <a id="13013" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Function Operator">+</a> <a id="13015" class="Number">3</a> <a id="13017" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13019" class="Number">5</a>
<a id="13021" class="Symbol">_</a> <a id="13023" class="Symbol">=</a>
  <a id="13027" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3868" class="Function Operator">begin</a>
    <a id="13037" class="Number">2</a> <a id="13039" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Function Operator">+</a> <a id="13041" class="Number">3</a>
  <a id="13045" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>    <a id="13052" class="Comment">-- is shorthand for</a>
    <a id="13076" class="Symbol">(</a><a id="13077" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13081" class="Symbol">(</a><a id="13082" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13086" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1049" class="InductiveConstructor">zero</a><a id="13090" class="Symbol">))</a> <a id="13093" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Function Operator">+</a> <a id="13095" class="Symbol">(</a><a id="13096" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13100" class="Symbol">(</a><a id="13101" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13105" class="Symbol">(</a><a id="13106" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13110" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1049" class="InductiveConstructor">zero</a><a id="13114" class="Symbol">)))</a>
  <a id="13120" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>    <a id="13127" class="Comment">-- inductive case</a>
    <a id="13149" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13153" class="Symbol">((</a><a id="13155" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13159" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1049" class="InductiveConstructor">zero</a><a id="13163" class="Symbol">)</a> <a id="13165" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Function Operator">+</a> <a id="13167" class="Symbol">(</a><a id="13168" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13172" class="Symbol">(</a><a id="13173" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13177" class="Symbol">(</a><a id="13178" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13182" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1049" class="InductiveConstructor">zero</a><a id="13186" class="Symbol">))))</a>
  <a id="13193" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>    <a id="13200" class="Comment">-- inductive case</a>
    <a id="13222" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13226" class="Symbol">(</a><a id="13227" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13231" class="Symbol">(</a><a id="13232" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1049" class="InductiveConstructor">zero</a> <a id="13237" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Function Operator">+</a> <a id="13239" class="Symbol">(</a><a id="13240" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13244" class="Symbol">(</a><a id="13245" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13249" class="Symbol">(</a><a id="13250" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13254" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1049" class="InductiveConstructor">zero</a><a id="13258" class="Symbol">)))))</a>
  <a id="13266" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>    <a id="13273" class="Comment">-- base case</a>
    <a id="13290" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13294" class="Symbol">(</a><a id="13295" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13299" class="Symbol">(</a><a id="13300" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13304" class="Symbol">(</a><a id="13305" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13309" class="Symbol">(</a><a id="13310" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13314" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1049" class="InductiveConstructor">zero</a><a id="13318" class="Symbol">))))</a>
  <a id="13325" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>    <a id="13332" class="Comment">-- is longhand for</a>
    <a id="13355" class="Number">5</a>
  <a id="13359" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4166" class="Function Operator">∎</a>{% endraw %}</pre>
We can write the same derivation more compactly by only
expanding shorthand as needed.
<pre class="Agda">{% raw %}<a id="13472" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#13472" class="Function">_</a> <a id="13474" class="Symbol">:</a> <a id="13476" class="Number">2</a> <a id="13478" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Function Operator">+</a> <a id="13480" class="Number">3</a> <a id="13482" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13484" class="Number">5</a>
<a id="13486" class="Symbol">_</a> <a id="13488" class="Symbol">=</a>
  <a id="13492" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3868" class="Function Operator">begin</a>
    <a id="13502" class="Number">2</a> <a id="13504" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Function Operator">+</a> <a id="13506" class="Number">3</a>
  <a id="13510" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
    <a id="13518" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13522" class="Symbol">(</a><a id="13523" class="Number">1</a> <a id="13525" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Function Operator">+</a> <a id="13527" class="Number">3</a><a id="13528" class="Symbol">)</a>
  <a id="13532" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
    <a id="13540" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13544" class="Symbol">(</a><a id="13545" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13549" class="Symbol">(</a><a id="13550" class="Number">0</a> <a id="13552" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Function Operator">+</a> <a id="13554" class="Number">3</a><a id="13555" class="Symbol">))</a>
  <a id="13560" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
    <a id="13568" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13572" class="Symbol">(</a><a id="13573" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="13577" class="Number">3</a><a id="13578" class="Symbol">)</a>
  <a id="13582" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
    <a id="13590" class="Number">5</a>
  <a id="13594" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4166" class="Function Operator">∎</a>{% endraw %}</pre>
The first line matches the inductive case by taking `m = 1` and `n = 3`,
the second line matches the inductive case by taking `m = 0` and `n = 3`,
and the third line matches the base case by taking `n = 3`.

Both derivations consist of a signature, giving a type, and a binding,
giving a term of the given type.  Here we use the dummy name `_`.  The
dummy name can be reused, and is convenient for examples.  Names other
than `_` must be used only once in a module.

Here the type is `2 + 3 ≡ 5` and the term provides *evidence* for the
corresponding equation, here written in tabular form as a chain of equations.
The chain starts with `begin` and finishes with `∎` (pronounced "qed" or
"tombstone", the latter from its appearance), and consists of a series
of terms separated by `≡⟨⟩`.

In fact, both proofs are longer than need be, and Agda is satisfied
with the following.
<pre class="Agda">{% raw %}<a id="14497" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#14497" class="Function">_</a> <a id="14499" class="Symbol">:</a> <a id="14501" class="Number">2</a> <a id="14503" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Function Operator">+</a> <a id="14505" class="Number">3</a> <a id="14507" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="14509" class="Number">5</a>
<a id="14511" class="Symbol">_</a> <a id="14513" class="Symbol">=</a> <a id="14515" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>
Agda knows how to compute the value of `2 + 3`, and so can immediately
check it is the same as `5`.  A binary relation is said to be *reflexive* if
it holds between a value and itself.  Evidence that a value is equal to
itself is written `refl`.

In the chains of equations, all Agda checks is that each term
simplifies to the same value. If we jumble the equations, omit lines, or
add extraneous lines it will still be accepted.  It's up to us to write
the equations in an order that makes sense to the reader.

Here `2 + 3 ≡ 5` is a type, and the chains of equations (and also
`refl`) are terms of the given type; alternatively, one can think of
each term as *evidence* for the assertion `2 + 3 ≡ 5`.  This duality
of interpretation---of a type as a proposition, and of a term as
evidence---is central to how we formalise concepts in Agda, and will
be a running theme throughout this book.

Note that when we use the word *evidence* it is nothing equivocal.  It
is not like testimony in a court which must be weighed to determine
whether the witness is trustworthy.  Rather, it is ironclad.  The
other word for evidence, which we will use interchangeably, is *proof*.

### Exercise (`3+4`)

Compute `3 + 4`, writing out your reasoning as a chain of equations.


## Multiplication

Once we have defined addition, we can define multiplication
as repeated addition.
<pre class="Agda">{% raw %}<a id="_*_"></a><a id="15909" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#15909" class="Function Operator">_*_</a> <a id="15913" class="Symbol">:</a> <a id="15915" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1033" class="Datatype">ℕ</a> <a id="15917" class="Symbol">→</a> <a id="15919" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1033" class="Datatype">ℕ</a> <a id="15921" class="Symbol">→</a> <a id="15923" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1033" class="Datatype">ℕ</a>
<a id="15925" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1049" class="InductiveConstructor">zero</a> <a id="15930" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#15909" class="Function Operator">*</a> <a id="15932" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#15932" class="Bound">n</a>     <a id="15938" class="Symbol">=</a>  <a id="15941" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1049" class="InductiveConstructor">zero</a> 
<a id="15947" class="Symbol">(</a><a id="15948" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="15952" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#15952" class="Bound">m</a><a id="15953" class="Symbol">)</a> <a id="15955" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#15909" class="Function Operator">*</a> <a id="15957" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#15957" class="Bound">n</a>  <a id="15960" class="Symbol">=</a>  <a id="15963" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#15957" class="Bound">n</a> <a id="15965" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Function Operator">+</a> <a id="15967" class="Symbol">(</a><a id="15968" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#15952" class="Bound">m</a> <a id="15970" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#15909" class="Function Operator">*</a> <a id="15972" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#15957" class="Bound">n</a><a id="15973" class="Symbol">)</a>{% endraw %}</pre>

Again, rewriting gives us two familiar equations.

    0       * n  ≡  0
    (1 + m) * n  ≡  n + (m * n)

The first follows because zero times anything is zero, and the second
follows because multiplication distributes over addition.
In its most general form, distribution of multiplication over addition
is written

    (m + n) * p  ≡  (m * p) + (n * p)

We get the second equation from this one by taking `m` to be `1`, `n`
to be `m`, and `p` to be `n`, and then using the fact that one is an
identity for multiplication, so `1 * n = n`.

Again, the definition is well-founded in that multiplication of
larger numbers is defined in terms of multiplication of smaller numbers.
 
For example, let's multiply two and three.
<pre class="Agda">{% raw %}<a id="16723" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#16723" class="Function">_</a> <a id="16725" class="Symbol">=</a>
  <a id="16729" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3868" class="Function Operator">begin</a>
    <a id="16739" class="Number">2</a> <a id="16741" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#15909" class="Function Operator">*</a> <a id="16743" class="Number">3</a>
  <a id="16747" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>    <a id="16754" class="Comment">-- inductive case</a>
    <a id="16776" class="Number">3</a> <a id="16778" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Function Operator">+</a> <a id="16780" class="Symbol">(</a><a id="16781" class="Number">1</a> <a id="16783" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#15909" class="Function Operator">*</a> <a id="16785" class="Number">3</a><a id="16786" class="Symbol">)</a>
  <a id="16790" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>    <a id="16797" class="Comment">-- inductive case</a>
    <a id="16819" class="Number">3</a> <a id="16821" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Function Operator">+</a> <a id="16823" class="Symbol">(</a><a id="16824" class="Number">3</a> <a id="16826" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Function Operator">+</a> <a id="16828" class="Symbol">(</a><a id="16829" class="Number">0</a> <a id="16831" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#15909" class="Function Operator">*</a> <a id="16833" class="Number">3</a><a id="16834" class="Symbol">))</a>
  <a id="16839" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>    <a id="16846" class="Comment">-- base case</a>
    <a id="16863" class="Number">3</a> <a id="16865" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Function Operator">+</a> <a id="16867" class="Symbol">(</a><a id="16868" class="Number">3</a> <a id="16870" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Function Operator">+</a> <a id="16872" class="Number">0</a><a id="16873" class="Symbol">)</a>
  <a id="16877" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>    <a id="16884" class="Comment">-- simplify</a>
    <a id="16900" class="Number">6</a>
  <a id="16904" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4166" class="Function Operator">∎</a>{% endraw %}</pre>
The first line matches the inductive case by taking `m = 1` and `n = 3`,
The second line matches the inductive case by taking `m = 0` and `n = 3`,
and the third line matches the base case by taking `n = 3`.
Here we have omitted the signature declaring `_ : 2 * 3 ≡ 6`, since
it can easily be inferred from the corresponding term.


### Exercise (`3*4`)

Compute `3 * 4`.


### Exercise (`_^_`).

Define exponentiation, which is given by the following equations.

    n ^ 0        =  1
    n ^ (1 + m)  =  n * (n ^ m)

Check that `3 ^ 4` is `81`.


## Monus

We can also define subtraction.  Since there are no negative
natural numbers, if we subtract a larger number from a smaller
number we will take the result to be zero.  This adaption of
subtraction to naturals is called *monus* (as compared to *minus*).

Monus is our first example of a definition that uses pattern
matching against both arguments.
<pre class="Agda">{% raw %}<a id="_∸_"></a><a id="17836" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#17836" class="Function Operator">_∸_</a> <a id="17840" class="Symbol">:</a> <a id="17842" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1033" class="Datatype">ℕ</a> <a id="17844" class="Symbol">→</a> <a id="17846" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1033" class="Datatype">ℕ</a> <a id="17848" class="Symbol">→</a> <a id="17850" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1033" class="Datatype">ℕ</a>
<a id="17852" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#17852" class="Bound">m</a>       <a id="17860" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#17836" class="Function Operator">∸</a> <a id="17862" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1049" class="InductiveConstructor">zero</a>     <a id="17871" class="Symbol">=</a>  <a id="17874" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#17852" class="Bound">m</a>
<a id="17876" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1049" class="InductiveConstructor">zero</a>    <a id="17884" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#17836" class="Function Operator">∸</a> <a id="17886" class="Symbol">(</a><a id="17887" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="17891" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#17891" class="Bound">n</a><a id="17892" class="Symbol">)</a>  <a id="17895" class="Symbol">=</a>  <a id="17898" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1049" class="InductiveConstructor">zero</a>
<a id="17903" class="Symbol">(</a><a id="17904" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="17908" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#17908" class="Bound">m</a><a id="17909" class="Symbol">)</a> <a id="17911" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#17836" class="Function Operator">∸</a> <a id="17913" class="Symbol">(</a><a id="17914" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#1060" class="InductiveConstructor">suc</a> <a id="17918" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#17918" class="Bound">n</a><a id="17919" class="Symbol">)</a>  <a id="17922" class="Symbol">=</a>  <a id="17925" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#17908" class="Bound">m</a> <a id="17927" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#17836" class="Function Operator">∸</a> <a id="17929" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#17918" class="Bound">n</a>{% endraw %}</pre>
We can do a simple analysis to show that all the cases are covered.

  * The second argument is either `zero` or `suc n` for some `n`.
    + If it is `zero`, then the first equation applies.
    + If it is `suc n`, then the first argument is either `zero`
      or `suc m` for some `m`.
      - If it is `zero`, then the second equation applies.
      - If it is `suc m`, then the third equation applies.

Again, the recursive definition is well-founded because
monus on bigger numbers is defined in terms of monus on
small numbers.

For example, let's subtract two from three.
<pre class="Agda">{% raw %}<a id="18533" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#18533" class="Function">_</a> <a id="18535" class="Symbol">=</a>
  <a id="18539" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3868" class="Function Operator">begin</a>
     <a id="18550" class="Number">3</a> <a id="18552" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#17836" class="Function Operator">∸</a> <a id="18554" class="Number">2</a>
  <a id="18558" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
     <a id="18567" class="Number">2</a> <a id="18569" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#17836" class="Function Operator">∸</a> <a id="18571" class="Number">1</a>
  <a id="18575" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
     <a id="18584" class="Number">1</a> <a id="18586" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#17836" class="Function Operator">∸</a> <a id="18588" class="Number">0</a>
  <a id="18592" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
     <a id="18601" class="Number">1</a>
  <a id="18605" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4166" class="Function Operator">∎</a>{% endraw %}</pre>
We did not use the third equation at all, but it will be required
if we try to subtract a smaller number from a larger one.
<pre class="Agda">{% raw %}<a id="18755" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#18755" class="Function">_</a> <a id="18757" class="Symbol">=</a>
  <a id="18761" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3868" class="Function Operator">begin</a>
     <a id="18772" class="Number">2</a> <a id="18774" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#17836" class="Function Operator">∸</a> <a id="18776" class="Number">3</a>
  <a id="18780" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
     <a id="18789" class="Number">1</a> <a id="18791" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#17836" class="Function Operator">∸</a> <a id="18793" class="Number">2</a>
  <a id="18797" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
     <a id="18806" class="Number">0</a> <a id="18808" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#17836" class="Function Operator">∸</a> <a id="18810" class="Number">1</a>
  <a id="18814" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
     <a id="18823" class="Number">0</a>
  <a id="18827" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4166" class="Function Operator">∎</a>{% endraw %}</pre>

### Exercise (`5∸3`, `3∸5`)

Compute `5 ∸ 3` and `3 ∸ 5`.


## Precedence

We often use *precedence* to avoid writing too many parentheses.
Application *binds more tightly than* (or *has precedence over*) any
operator, and so we may write `suc m + n` to mean `(suc m) + n`.
As another example, we say that multiplication binds more tightly than
addition, and so write `n + m * n` to mean `n + (m * n)`.
We also sometimes say that addition *associates to the left*, and
so write `m + n + p` to mean `(m + n) + p`.

In Agda the precedence and associativity of infix operators
needs to be declared.
<pre class="Agda">{% raw %}<a id="19450" class="Keyword">infixl</a> <a id="19457" class="Number">7</a>  <a id="19460" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#15909" class="Primitive Operator">_*_</a>
<a id="19464" class="Keyword">infixl</a> <a id="19471" class="Number">6</a>  <a id="19474" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Primitive Operator">_+_</a>  <a id="19479" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#17836" class="Primitive Operator">_∸_</a>{% endraw %}</pre>
This states that operator `_*_` has precedence level 7, and that
operators `_+_` and `_∸_` have precedence level 6.  Multiplication
binds more tightly that addition or subtraction because it has a
higher precedence.  Writing `infixl` indicates that all three
operators associate to the left.  One can also write `infixr` to
indicate that an operator associates to the right, or just `infix` to
indicate that parentheses are always required to disambiguate.


## Currying

We have chosen to represent a function of two arguments in terms
of a function of the first argument that returns a function of the
second argument.  This trick goes by the name *currying*.

Agda, like other functional languages such as
ML and Haskell, is designed to make currying easy to use.  Function
arrows associate to the left and application associates to the right.

    ℕ → ℕ → ℕ    stands for    ℕ → (ℕ → ℕ)

and

    _+_ 2 3    stands for    (_+_ 2) 3

The term `_+_ 2` by itself stands for the function that adds two to
its argument, hence applying it to three yields five.

Currying is named for Haskell Curry, after whom the programming
language Haskell is also named.  Curry's work dates to the 1930's.
When I first learned about currying, I was told it was misattributed,
since the same idea was previously proposed by Moses Schönfinkel in
the 1920's.  I was told a joke: "It should be called schönfinkeling,
but currying is tastier". Only later did I learn that the explanation
of the misattribution was itself a misattribution.  The idea actually
appears in the *Begriffschrift* of Gottlob Frege, published in 1879.
We should call it frigging!


## The story of creation, revisited

Just as our inductive definition defines the naturals in terms of the
naturals, so does our recursive definition define addition in terms
of addition.

Again, it is possible to assign our definition a meaning without
resorting to unpermitted circularities.  We do so by reducing our
definition to equivalent inference rules for judgements about equality.

    n : ℕ
    ------------
    zero + n = n

    m + n = p
    -------------------
    (suc m) + n = suc p

Here we assume we have already defined the infinite set of natural
numbers, specifying the meaning of the judgment `n : ℕ`.  The first
inference rule is the base case, and corresponds to line (i) of the
definition.  It asserts that if `n` is a natural number then adding
zero to it gives `n`.  The second inference rule is the inductive
case, and corresponds to line (ii) of the definition. It asserts that
if adding `m` and `n` gives `p`, then adding `suc m` and `n` gives
`suc p`.

Again we resort to a creation story, where this time we are
concerned with judgements about addition.

    -- in the beginning, we know nothing about addition

Now, we apply the rules to all the judgment we know about.
The base case tells us that `zero + n = n` for every natural `n`,
so we add all those equations.  The inductive case tells us that if
`m + n = p` (on the day before today) then `suc m + n = suc p`
(today).  We didn't know any equations about addition before today,
so that rule doesn't give us any new equations.

    -- on the first day, we know about addition of 0
    0 + 0 = 0     0 + 1 = 1    0 + 2 = 2     ...

Then we repeat the process, so on the next day we know about all the
equations from the day before, plus any equations added by the rules.
The base case tells us nothing new, but now the inductive case adds
more equations.

    -- on the second day, we know about addition of 0 and 1
    0 + 0 = 0     0 + 1 = 1     0 + 2 = 2     0 + 3 = 3     ...
    1 + 0 = 1     1 + 1 = 2     1 + 2 = 3     1 + 3 = 4     ...

And we repeat the process again.  

    -- on the third day, we know about addition of 0, 1, and 2
    0 + 0 = 0     0 + 1 = 1     0 + 2 = 2     0 + 3 = 3     ...
    1 + 0 = 1     1 + 1 = 2     1 + 2 = 3     1 + 3 = 4     ...
    2 + 0 = 2     2 + 1 = 3     2 + 2 = 4     2 + 3 = 5     ...

You've got the hang of it by now.

    -- on the fourth day, we know about addition of 0, 1, 2, and 3
    0 + 0 = 0     0 + 1 = 1     0 + 2 = 2     0 + 3 = 3     ...
    1 + 0 = 1     1 + 1 = 2     1 + 2 = 3     1 + 3 = 4     ...
    2 + 0 = 2     2 + 1 = 3     2 + 2 = 4     2 + 3 = 5     ...
    3 + 0 = 3     3 + 1 = 4     3 + 2 = 5     3 + 3 = 6     ...

The process continues.  On the *m*th day we will know all the
equations where the first number is less than *m*.

As we can see, the reasoning that justifies inductive and recursive
definitions is quite similar.  They might be considered two sides of
the same coin.


## The story of creation, finitely {#finite-creation}

The above story was told in a stratified way.  First, we create
the infinite set of naturals.  We take that set as given when
creating instances of addition, so even on day one we have an
infinite set of instances.

Instead, we could choose to create both the naturals and the instances
of addition at the same time. Then on any day there would be only
a finite set of instances.

    -- in the beginning, we know nothing

Now, we apply the rules to all the judgment we know about.  Only the
base case for naturals applies.

    -- on the first day, we know zero
    0 : ℕ

Again, we apply all the rules we know.  This gives us a new natural,
and our first equation about addition.

    -- on the second day, we know one and all sums that yield zero
    0 : ℕ
    1 : ℕ    0 + 0 = 0

Then we repeat the process.  We get one more equation about addition
from the base case, and also get an equation from the inductive case,
applied to equation of the previous day.

    -- on the third day, we know two and all sums that yield one
    0 : ℕ
    1 : ℕ    0 + 0 = 0
    2 : ℕ    0 + 1 = 1   1 + 0 = 1

You've got the hang of it by now.

    -- on the fourth day, we know three and all sums that yield two
    0 : ℕ
    1 : ℕ    0 + 0 = 0
    2 : ℕ    0 + 1 = 1   1 + 0 = 1
    3 : ℕ    0 + 2 = 2   1 + 1 = 2    2 + 0 = 2

On the *n*th day there will be *n* distinct natural numbers, and *n ×
(n-1) / 2* equations about addition.  The number *n* and all equations
for addition of numbers less than *n* first appear by day *n+1*.
This gives an entirely finitist view of infinite sets of data and
equations relating the data.


## Writing definitions interactively

Agda is designed to be used with the Emacs text editor, and the two
in combination provide features that help to create proofs interactively.

Begin by typing

    _+_ : ℕ → ℕ → ℕ
    m + n = ?

The question mark indicates that you would like Agda to help with filling
in that part of the code. If you type `^C ^L` (control-C followed by control-L)
the question mark will be replaced.

    _+_ : ℕ → ℕ → ℕ
    m + n = { }0

The empty braces are called a *hole*, and 0 is a number used for
referring to the hole.  The hole will display highlighted in green.
Emacs will also create a window displaying the text

    ?0 : ℕ

to indicate that hole 0 is to be filled in with a term of type `ℕ`.

We wish to define addition by recursion on the first argument.
Move the cursor into the hole and type `^C ^C`.   You will be given
the prompt:

    pattern variables to case (empty for split on result):

Typing `m` will cause a split on that variable, resulting
in an update to the code.

    _+_ : ℕ → ℕ → ℕ
    zero + n = { }0
    suc m + n = { }1

There are now two holes, and the window at the bottom tells you the
required type of each.

    ?0 : ℕ
    ?1 : ℕ

Going into hole 0 and type `^C ^,` will display information on the
required type of the hole, and what free variables are available.

    Goal: ℕ
    ————————————————————————————————————————————————————————————
    n : ℕ

This strongly suggests filling the hole with `n`.  After the hole is
filled, you can type `^C ^space`, which will remove the hole.

    _+_ : ℕ → ℕ → ℕ
    zero + n = n
    suc m + n = { }1

Again, going into hole 1 and type `^C ^,` will display information on the
required type of the hole, and what free variables are available.

    Goal: ℕ
    ————————————————————————————————————————————————————————————
    n : ℕ
    m : ℕ

Going into the hole and type `^C ^R` will fill it in with a constructor
(if there is a unique choice) or tell you what constructors you might use,
if there is a choice.  In this case, it displays the following.

    Don't know which constructor to introduce of zero or suc

Filling the hole with `suc ?` and typing `^C ^space` results in the following.

    _+_ : ℕ → ℕ → ℕ
    zero + n = n
    suc m + n = suc { }1

Going into the new hole and typing `^C ^,` gives similar information to before.

    Goal: ℕ
    ————————————————————————————————————————————————————————————
    n : ℕ
    m : ℕ

We can fill the hole with `m + n` and type `^C ^space` to complete the program.

    _+_ : ℕ → ℕ → ℕ
    zero + n = n
    suc m + n = suc (m + n)

Exploiting interaction to this degree is probably not helpful for a program this
simple, but the same techniques can help with more complex programs.  Even for
a program this simple, using `^C ^C` to split cases can be helpful.


## More pragmas

Including the lines
<pre class="Agda">{% raw %}<a id="28631" class="Symbol">{-#</a> <a id="28635" class="Keyword">BUILTIN</a> NATPLUS <a id="28651" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#11080" class="Primitive Operator">_+_</a> <a id="28655" class="Symbol">#-}</a>
<a id="28659" class="Symbol">{-#</a> <a id="28663" class="Keyword">BUILTIN</a> NATTIMES <a id="28680" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#15909" class="Primitive Operator">_*_</a> <a id="28684" class="Symbol">#-}</a>
<a id="28688" class="Symbol">{-#</a> <a id="28692" class="Keyword">BUILTIN</a> NATMINUS <a id="28709" href="{% endraw %}{{ site.baseurl }}{% link out/Naturals.md %}{% raw %}#17836" class="Primitive Operator">_∸_</a> <a id="28713" class="Symbol">#-}</a>{% endraw %}</pre>
tells Agda that these three operators correspond to the usual ones,
and enables it to perform these computations using the corresponding
Haskell operators on the arbitrary-precision integer type.
Representing naturals with `zero` and `suc` requires time proportional
to *m* to add *m* and *n*, whereas representing naturals as integers
in Haskell requires time proportional to the larger of the logarithms
(base 2) of *m* and *n*.  Similarly, representing naturals with `zero`
and `suc` requires time proportional to the product of *m* and *n* to
multiply *m* and *n*, whereas representing naturals as integers in
Haskell requires time proportional to the sum of the logarithms of *m*
and *n*.


## Standard library

At the end of each chapter, we will show where to find relevant
definitions in the standard library.  The naturals, constructors for
them, and basic operators upon them, are defined in the standard
library module `Data.Nat`.

    import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)

Normally, we will show an import as running code, so Agda will
complain if we attempt to import a definition that is not available.
This time, however, we have only shown the import as a comment.  Both
this chapter and the standard library invoke the `NATURAL` pragma, the
former on `ℕ`, and the latter on the equivalent type `Data.Nat.ℕ`.
Such a pragma can only be invoked once, as invoking it twice would
raise confusion as to whether `2` is a value of type `ℕ` or type
`Data.Nat.ℕ`.  Similar confusions arise if other pragmas are invoked
twice. For this reason, we will usually avoid pragmas in future chapters.
Information on pragmas can be found in the Agda documentation.


## Unicode

This chapter uses the following unicode.

    ℕ  U+2115  DOUBLE-STRUCK CAPITAL N (\bN)  
    →  U+2192  RIGHTWARDS ARROW (\to, \r)
    ∸  U+2238  DOT MINUS (\.-)
    ≡  U+2261  IDENTICAL TO (\==)  =
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)

Each line consists of the Unicode character (`ℕ`), the corresponding
code point (`U+2115`), the name of the character (`DOUBLE-STRUCK CAPITAL N`),
and the sequence to type into Emacs to generate the character (`\bN`).

The command `\r` gives access to a wide variety of rightward arrows.
After typing `\r`, one can access the many available arrows by using
the left, right, up, and down keys to navigate.  The command remembers
where you navigated to the last time, and starts with the same
character next time.

In place of left, right, up, and down keys, one may also use control characters.

    ^B  left (Backward)
    ^F  right (Forward)
    ^P  up (uP)
    ^N  down (dowN)

We write `^B` to stand for control-B, and similarly.  One can also navigate
left and write by typing the digits that appear in the displayed list.


