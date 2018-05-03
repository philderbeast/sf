---
title     : "Stlc: The Simply Typed Lambda-Calculus"
layout    : page
permalink : /Stlc
---

The _lambda-calculus_, first published by the logician Alonzo Church in
1932, is a core calculus with only three syntactic constructs:
variables, abstraction, and application.  It embodies the concept of
_functional abstraction_, which shows up in almost every programming
language in some form (as functions, procedures, or methods).
The _simply-typed lambda calculus_ (or STLC) is a variant of the
lambda calculus published by Church in 1940.  It has just the three
constructs above for function types, plus whatever else is required
for base types. Church had a minimal base type with no operations;
we will be slightly more pragmatic and choose booleans as our base type.

This chapter formalises the STLC (syntax, small-step semantics, and typing rules),
and the next chapter reviews its main properties (progress and preservation).
The new technical challenges arise from the mechanisms of
_variable binding_ and _substitution_.

<!--
We've already seen how to formalize a language with
variables ([Imp]({{ "Imp" | relative_url }})).
There, however, the variables were all global.
In the STLC, we need to handle the variables that name the
parameters to functions, and these are _bound_ variables.
Moreover, instead of just looking up variables in a global store,
we'll need to reduce function applications by _substituting_
arguments for parameters in function bodies.
-->

We choose booleans as our base type for simplicity.  At the end of the
chapter we'll see how to add numbers as a base type, and in later
chapters we'll enrich STLC with useful constructs like pairs, sums,
lists, records, subtyping, and mutable state.

## Imports

<pre class="Agda">{% raw %}<a id="1756" class="Keyword">open</a> <a id="1761" class="Keyword">import</a> <a id="1768" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}" class="Module">Maps</a> <a id="1773" class="Keyword">using</a> <a id="1779" class="Symbol">(</a><a id="1780" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2171" class="Datatype">Id</a><a id="1782" class="Symbol">;</a> <a id="1784" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2188" class="InductiveConstructor">id</a><a id="1786" class="Symbol">;</a> <a id="1788" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2509" class="Function Operator">_≟_</a><a id="1791" class="Symbol">;</a> <a id="1793" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10132" class="Function">PartialMap</a><a id="1803" class="Symbol">;</a> <a id="1805" class="Keyword">module</a> <a id="1812" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10221" class="Module">PartialMap</a><a id="1822" class="Symbol">)</a>
<a id="1824" class="Keyword">open</a> <a id="1829" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10221" class="Module">PartialMap</a> <a id="1840" class="Keyword">using</a> <a id="1846" class="Symbol">(</a><a id="1847" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10265" class="Function">∅</a><a id="1848" class="Symbol">;</a> <a id="1850" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#11919" class="Function">just-injective</a><a id="1864" class="Symbol">)</a> <a id="1866" class="Keyword">renaming</a> <a id="1875" class="Symbol">(</a><a id="1876" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10368" class="Function Operator">_,_↦_</a> <a id="1882" class="Symbol">to</a> <a id="1885" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10368" class="Function Operator">_,_∶_</a><a id="1890" class="Symbol">)</a>
<a id="1892" class="Keyword">open</a> <a id="1897" class="Keyword">import</a> <a id="1904" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="1913" class="Keyword">using</a> <a id="1919" class="Symbol">(</a><a id="1920" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1921" class="Symbol">)</a>
<a id="1923" class="Keyword">open</a> <a id="1928" class="Keyword">import</a> <a id="1935" href="https://agda.github.io/agda-stdlib/Data.Maybe.html" class="Module">Data.Maybe</a> <a id="1946" class="Keyword">using</a> <a id="1952" class="Symbol">(</a><a id="1953" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype">Maybe</a><a id="1958" class="Symbol">;</a> <a id="1960" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1603" class="InductiveConstructor">just</a><a id="1964" class="Symbol">;</a> <a id="1966" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1664" class="InductiveConstructor">nothing</a><a id="1973" class="Symbol">)</a>
<a id="1975" class="Keyword">open</a> <a id="1980" class="Keyword">import</a> <a id="1987" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="2004" class="Keyword">using</a> <a id="2010" class="Symbol">(</a><a id="2011" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#534" class="Datatype">Dec</a><a id="2014" class="Symbol">;</a> <a id="2016" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#570" class="InductiveConstructor">yes</a><a id="2019" class="Symbol">;</a> <a id="2021" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#597" class="InductiveConstructor">no</a><a id="2023" class="Symbol">;</a> <a id="2025" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#464" class="Function Operator">¬_</a><a id="2027" class="Symbol">)</a>
<a id="2029" class="Keyword">open</a> <a id="2034" class="Keyword">import</a> <a id="2041" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="2079" class="Keyword">using</a> <a id="2085" class="Symbol">(</a><a id="2086" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="2089" class="Symbol">;</a> <a id="2091" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator">_≢_</a><a id="2094" class="Symbol">;</a> <a id="2096" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="2100" class="Symbol">)</a>{% endraw %}</pre>

## Syntax

We have just two types.

  * Functions, `A ⇒ B`
  * Booleans, `𝔹`

We require some form of base type, because otherwise the set of types
would be empty. Church used a trivial base type `o` with no operations.
For us, it is more convenient to use booleans. Later we will consider
numbers as a base type.

Here is the syntax of types in BNF.

    A, B, C  ::=  A ⇒ B | 𝔹

And here it is formalised in Agda.

<pre class="Agda">{% raw %}<a id="2544" class="Keyword">infixr</a> <a id="2551" class="Number">20</a> <a id="2554" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">_⇒_</a>

<a id="2559" class="Keyword">data</a> <a id="Type"></a><a id="2564" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2564" class="Datatype">Type</a> <a id="2569" class="Symbol">:</a> <a id="2571" class="PrimitiveType">Set</a> <a id="2575" class="Keyword">where</a>
  <a id="Type._⇒_"></a><a id="2583" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">_⇒_</a> <a id="2587" class="Symbol">:</a> <a id="2589" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2564" class="Datatype">Type</a> <a id="2594" class="Symbol">→</a> <a id="2596" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2564" class="Datatype">Type</a> <a id="2601" class="Symbol">→</a> <a id="2603" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2564" class="Datatype">Type</a>
  <a id="Type.𝔹"></a><a id="2610" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="2612" class="Symbol">:</a> <a id="2614" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2564" class="Datatype">Type</a>{% endraw %}</pre>

Terms have six constructs. Three are for the core lambda calculus:

  * Variables, `` ` x ``
  * Abstractions, `λ[ x ∶ A ] N`
  * Applications, `L · M`

and three are for the base type, booleans:

  * True, `true`
  * False, `false`
  * Conditions, `if L then M else N`

Abstraction is also called lambda abstraction, and is the construct
from which the calculus takes its name. 

With the exception of variables, each term form either constructs
a value of a given type (abstractions yield functions, true and
false yield booleans) or deconstructs it (applications use functions,
conditionals use booleans). We will see this again when we come
to the rules for assigning types to terms, where constructors
correspond to introduction rules and deconstructors to eliminators.

Here is the syntax of terms in BNF.

    L, M, N  ::=  ` x | λ[ x ∶ A ] N | L · M | true | false | if L then M else N

And here it is formalised in Agda.

<pre class="Agda">{% raw %}<a id="3575" class="Keyword">infixl</a> <a id="3582" class="Number">20</a> <a id="3585" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">_·_</a>
<a id="3589" class="Keyword">infix</a>  <a id="3596" class="Number">15</a> <a id="3599" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[_∶_]_</a>
<a id="3607" class="Keyword">infix</a>  <a id="3614" class="Number">15</a> <a id="3617" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if_then_else_</a>

<a id="3632" class="Keyword">data</a> <a id="Term"></a><a id="3637" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="3642" class="Symbol">:</a> <a id="3644" class="PrimitiveType">Set</a> <a id="3648" class="Keyword">where</a>
  <a id="Term.`"></a><a id="3656" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="3658" class="Symbol">:</a> <a id="3660" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2171" class="Datatype">Id</a> <a id="3663" class="Symbol">→</a> <a id="3665" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a>
  <a id="Term.λ[_∶_]_"></a><a id="3672" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[_∶_]_</a> <a id="3680" class="Symbol">:</a> <a id="3682" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2171" class="Datatype">Id</a> <a id="3685" class="Symbol">→</a> <a id="3687" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2564" class="Datatype">Type</a> <a id="3692" class="Symbol">→</a> <a id="3694" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="3699" class="Symbol">→</a> <a id="3701" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a>
  <a id="Term._·_"></a><a id="3708" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">_·_</a> <a id="3712" class="Symbol">:</a> <a id="3714" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="3719" class="Symbol">→</a> <a id="3721" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="3726" class="Symbol">→</a> <a id="3728" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a>
  <a id="Term.true"></a><a id="3735" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="3740" class="Symbol">:</a> <a id="3742" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a>
  <a id="Term.false"></a><a id="3749" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a> <a id="3755" class="Symbol">:</a> <a id="3757" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a>
  <a id="Term.if_then_else_"></a><a id="3764" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if_then_else_</a> <a id="3778" class="Symbol">:</a> <a id="3780" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="3785" class="Symbol">→</a> <a id="3787" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="3792" class="Symbol">→</a> <a id="3794" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="3799" class="Symbol">→</a> <a id="3801" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a>{% endraw %}</pre>

#### Special characters

We use the following special characters

    ⇒  U+21D2: RIGHTWARDS DOUBLE ARROW (\=>)
    `  U+0060: GRAVE ACCENT 
    λ  U+03BB:  GREEK SMALL LETTER LAMBDA (\Gl or \lambda)
    ∶  U+2236:  RATIO (\:)
    ·  U+00B7: MIDDLE DOT (\cdot)

Note that ∶ (U+2236 RATIO) is not the same as : (U+003A COLON).
Colon is reserved in Agda for declaring types. Everywhere that we
declare a type in the object language rather than Agda we use
ratio in place of colon.

Using ratio for this purpose is arguably a bad idea, because one must use context
rather than appearance to distinguish it from colon. Arguably, it might be
better to use a different symbol, such as `∈` or `::`.  We reserve `∈`
for use later to indicate that a variable appears free in a term, and
eschew `::` because we consider it too ugly.


#### Formal vs informal

In informal presentation of formal semantics, one uses choice of
variable name to disambiguate and writes `x` rather than `` ` x ``
for a term that is a variable. Agda requires we distinguish.
Often researchers use `var x` rather than `` ` x ``, but we chose
the latter since it is closer to the informal notation `x`.

Similarly, informal presentation often use the notations `A → B` for
functions, `λ x . N` for abstractions, and `L M` for applications.  We
cannot use these, because they overlap with the notation used by Agda.
In `λ[ x ∶ A ] N`, recall that Agda treats square brackets `[]` as
ordinary symbols, while round parentheses `()` and curly braces `{}`
have special meaning.  We would use `L @ M` for application, but
`@` has a reserved meaning in Agda.


#### Examples

Here are a couple of example terms, `not` of type
`𝔹 ⇒ 𝔹`, which complements its argument, and `two` of type
`(𝔹 ⇒ 𝔹) ⇒ 𝔹 ⇒ 𝔹` which takes a function and a boolean
and applies the function to the boolean twice.

<pre class="Agda">{% raw %}<a id="f"></a><a id="5677" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="x"></a><a id="5679" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a> <a id="y"></a><a id="5681" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5681" class="Function">y</a> <a id="5683" class="Symbol">:</a> <a id="5685" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2171" class="Datatype">Id</a>
<a id="5688" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a>  <a id="5691" class="Symbol">=</a>  <a id="5694" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2188" class="InductiveConstructor">id</a> <a id="5697" class="Number">0</a>
<a id="5699" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a>  <a id="5702" class="Symbol">=</a>  <a id="5705" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2188" class="InductiveConstructor">id</a> <a id="5708" class="Number">1</a>
<a id="5710" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5681" class="Function">y</a>  <a id="5713" class="Symbol">=</a>  <a id="5716" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2188" class="InductiveConstructor">id</a> <a id="5719" class="Number">2</a>

<a id="not"></a><a id="5722" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="two"></a><a id="5726" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5726" class="Function">two</a> <a id="5730" class="Symbol">:</a> <a id="5732" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> 
<a id="5738" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="5742" class="Symbol">=</a>  <a id="5745" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="5748" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a> <a id="5750" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="5752" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="5754" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="5756" class="Symbol">(</a><a id="5757" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="5760" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="5762" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a> <a id="5764" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="5769" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a> <a id="5775" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="5780" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a><a id="5784" class="Symbol">)</a>
<a id="5786" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5726" class="Function">two</a> <a id="5790" class="Symbol">=</a>  <a id="5793" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="5796" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="5798" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="5800" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="5802" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="5804" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="5806" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="5808" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="5811" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a> <a id="5813" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="5815" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="5817" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="5819" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="5821" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="5823" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="5825" class="Symbol">(</a><a id="5826" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="5828" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="5830" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="5832" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="5834" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a><a id="5835" class="Symbol">)</a>{% endraw %}</pre>


#### Bound and free variables

In an abstraction `λ[ x ∶ A ] N` we call `x` the _bound_ variable
and `N` the _body_ of the abstraction.  One of the most important
aspects of lambda calculus is that names of bound variables are
irrelevant.  Thus the five terms

* `` λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x) ``
* `` λ[ g ∶ 𝔹 ⇒ 𝔹 ] λ[ y ∶ 𝔹 ] ` g · (` g · ` y) ``
* `` λ[ fred ∶ 𝔹 ⇒ 𝔹 ] λ[ xander ∶ 𝔹 ] ` fred · (` fred · ` xander) ``
* `` λ[ 😈 ∶ 𝔹 ⇒ 𝔹 ] λ[ 😄 ∶ 𝔹 ] ` 😈 · (` 😈 · ` 😄) ``  
* `` λ[ x ∶ 𝔹 ⇒ 𝔹 ] λ[ f ∶ 𝔹 ] ` x · (` x · ` f) ``

are all considered equivalent.  This equivalence relation
is sometimes called _alpha renaming_.

As we descend from a term into its subterms, variables
that are bound may become free.  Consider the following terms.




* `` λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x) ``
  Both variable `f` and `x` are bound.

* `` λ[ x ∶ 𝔹 ] ` f · (` f · ` x) ``
  has `x` as a bound variable but `f` as a free variable.  

* `` ` f · (` f · ` x) ``
  has both `f` and `x` as free variables.

We say that a term with no free variables is _closed_; otherwise it is
_open_.  Of the three terms above, the first is closed and the other
two are open.  A formal definition of bound and free variables will be
given in the next chapter.

Different occurrences of a variable may be bound and free.
In the term 

    (λ[ x ∶ 𝔹 ] ` x) · ` x

the inner occurrence of `x` is bound while the outer occurrence is free.
Note that by alpha renaming, the term above is equivalent to

    (λ[ y ∶ 𝔹 ] ` y) · ` x

in which `y` is bound and `x` is free.  A common convention, called the
Barendregt convention, is to use alpha renaming to ensure that the bound
variables in a term are distinct from the free variables, which can
avoid confusions that may arise if bound and free variables have the
same names.

#### Special characters

    😈  U+1F608: SMILING FACE WITH HORNS
    😄  U+1F604: SMILING FACE WITH OPEN MOUTH AND SMILING EYES

#### Precedence

As in Agda, functions of two or more arguments are represented via
currying. This is made more convenient by declaring `_⇒_` to
associate to the right and `_·_` to associate to the left.
Thus,

* `(𝔹 ⇒ 𝔹) ⇒ 𝔹 ⇒ 𝔹` abbreviates `(𝔹 ⇒ 𝔹) ⇒ (𝔹 ⇒ 𝔹)`
* `two · not · true` abbreviates `(two · not) · true`.

We choose the binding strength for abstractions and conditionals
to be weaker than application. For instance,

* `` λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x) ``
  - abbreviates `` (λ[ f ∶ 𝔹 ⇒ 𝔹 ] (λ[ x ∶ 𝔹 ] (` f · (` f · ` x)))) ``
  - and not `` (λ[ f ∶ 𝔹 ⇒ 𝔹 ] (λ[ x ∶ 𝔹 ] ` f)) · (` f · ` x) ``.

<pre class="Agda">{% raw %}<a id="ex₁"></a><a id="8432" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#8432" class="Function">ex₁</a> <a id="8436" class="Symbol">:</a> <a id="8438" class="Symbol">(</a><a id="8439" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8441" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="8443" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a><a id="8444" class="Symbol">)</a> <a id="8446" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="8448" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8450" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="8452" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8454" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="8456" class="Symbol">(</a><a id="8457" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8459" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="8461" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a><a id="8462" class="Symbol">)</a> <a id="8464" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="8466" class="Symbol">(</a><a id="8467" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8469" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="8471" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a><a id="8472" class="Symbol">)</a>
<a id="8474" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#8432" class="Function">ex₁</a> <a id="8478" class="Symbol">=</a> <a id="8480" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="ex₂"></a><a id="8486" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#8486" class="Function">ex₂</a> <a id="8490" class="Symbol">:</a> <a id="8492" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5726" class="Function">two</a> <a id="8496" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="8498" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="8502" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="8504" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="8509" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="8511" class="Symbol">(</a><a id="8512" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5726" class="Function">two</a> <a id="8516" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="8518" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a><a id="8521" class="Symbol">)</a> <a id="8523" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="8525" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
<a id="8530" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#8486" class="Function">ex₂</a> <a id="8534" class="Symbol">=</a> <a id="8536" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="ex₃"></a><a id="8542" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#8542" class="Function">ex₃</a> <a id="8546" class="Symbol">:</a> <a id="8548" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="8551" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="8553" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="8555" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8557" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="8559" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8561" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="8563" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="8566" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a> <a id="8568" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="8570" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8572" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="8574" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="8576" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="8578" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="8580" class="Symbol">(</a><a id="8581" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="8583" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="8585" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="8587" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="8589" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a><a id="8590" class="Symbol">)</a>
      <a id="8598" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="8600" class="Symbol">(</a><a id="8601" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="8604" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="8606" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="8608" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8610" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="8612" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8614" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="8616" class="Symbol">(</a><a id="8617" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="8620" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a> <a id="8622" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="8624" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8626" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="8628" class="Symbol">(</a><a id="8629" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="8631" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="8633" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="8635" class="Symbol">(</a><a id="8636" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="8638" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="8640" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="8642" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="8644" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a><a id="8645" class="Symbol">))))</a>
<a id="8650" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#8542" class="Function">ex₃</a> <a id="8654" class="Symbol">=</a> <a id="8656" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>

#### Quiz

* What is the type of the following term?

    λ[ f ∶ 𝔹 ⇒ 𝔹 ] ` f · (` f  · true)

  1. `𝔹 ⇒ (𝔹 ⇒ 𝔹)`
  2. `(𝔹 ⇒ 𝔹) ⇒ 𝔹`
  3. `𝔹 ⇒ 𝔹 ⇒ 𝔹`
  4. `𝔹 ⇒ 𝔹`
  5. `𝔹`

  Give more than one answer if appropriate.

* What is the type of the following term?

    (λ[ f ∶ 𝔹 ⇒ 𝔹 ] ` f · (` f  · true)) · not

  1. `𝔹 ⇒ (𝔹 ⇒ 𝔹)`
  2. `(𝔹 ⇒ 𝔹) ⇒ 𝔹`
  3. `𝔹 ⇒ 𝔹 ⇒ 𝔹`
  4. `𝔹 ⇒ 𝔹`
  5. `𝔹`

  Give more than one answer if appropriate.

## Values

We only consider reduction of _closed_ terms,
those that contain no free variables.  We consider
a precise definition of free variables in
[StlcProp]({{ "StlcProp" | relative_url }}).

A term is a value if it is fully reduced.
For booleans, the situation is clear, `true` and
`false` are values, while conditionals are not.
For functions, applications are not values, because
we expect them to further reduce, and variables are
not values, because we focus on closed terms.
Following convention, we treat all abstractions
as values.

The predicate `Value M` holds if term `M` is a value.

<pre class="Agda">{% raw %}<a id="9717" class="Keyword">data</a> <a id="Value"></a><a id="9722" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9722" class="Datatype">Value</a> <a id="9728" class="Symbol">:</a> <a id="9730" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="9735" class="Symbol">→</a> <a id="9737" class="PrimitiveType">Set</a> <a id="9741" class="Keyword">where</a>
  <a id="Value.value-λ"></a><a id="9749" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9749" class="InductiveConstructor">value-λ</a>     <a id="9761" class="Symbol">:</a> <a id="9763" class="Symbol">∀</a> <a id="9765" class="Symbol">{</a><a id="9766" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9766" class="Bound">x</a> <a id="9768" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9768" class="Bound">A</a> <a id="9770" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9770" class="Bound">N</a><a id="9771" class="Symbol">}</a> <a id="9773" class="Symbol">→</a> <a id="9775" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9722" class="Datatype">Value</a> <a id="9781" class="Symbol">(</a><a id="9782" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="9785" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9766" class="Bound">x</a> <a id="9787" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="9789" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9768" class="Bound">A</a> <a id="9791" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="9793" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9770" class="Bound">N</a><a id="9794" class="Symbol">)</a>
  <a id="Value.value-true"></a><a id="9798" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9798" class="InductiveConstructor">value-true</a>  <a id="9810" class="Symbol">:</a> <a id="9812" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9722" class="Datatype">Value</a> <a id="9818" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
  <a id="Value.value-false"></a><a id="9825" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9825" class="InductiveConstructor">value-false</a> <a id="9837" class="Symbol">:</a> <a id="9839" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9722" class="Datatype">Value</a> <a id="9845" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a>{% endraw %}</pre>

We let `V` and `W` range over values.


#### Formal vs informal

In informal presentations of formal semantics, using
`V` as the name of a metavariable is sufficient to
indicate that it is a value. In Agda, we must explicitly
invoke the `Value` predicate.

#### Other approaches

An alternative is not to focus on closed terms,
to treat variables as values, and to treat
`λ[ x ∶ A ] N` as a value only if `N` is a value.
Indeed, this is how Agda normalises terms.
Formalising this approach requires a more sophisticated
definition of substitution.  Here we only
substitute closed terms for variables, while
the alternative requires the ability to substitute
open terms for variables.

## Substitution

The heart of lambda calculus is the operation of
substituting one term for a variable in another term.
Substitution plays a key role in defining the
operational semantics of function application.
For instance, we have

      (λ[ f ∶ 𝔹 ⇒ 𝔹 ] `f · (`f · true)) · not
    ⟹
      not · (not · true)

where we substitute `not` for `` `f `` in the body
of the function abstraction.

We write substitution as `N [ x := V ]`, meaning
substitute term `V` for free occurrences of variable `x` in term `N`,
or, more compactly, substitute `V` for `x` in `N`.
Substitution works if `V` is any closed term;
it need not be a value, but we use `V` since we
always substitute values.

Here are some examples.

* `` ` f [ f := not ] `` yields `` not ``
* `` true [ f := not ] `` yields `` true ``
* `` (` f · true) [ f := not ] `` yields `` not · true ``
* `` (` f · (` f · true)) [ f := not ] `` yields `` not · (not · true) ``
* `` (λ[ x ∶ 𝔹 ] ` f · (` f · ` x)) [ f := not ] `` yields `` λ[ x ∶ 𝔹 ] not · (not · ` x) ``
* `` (λ[ y ∶ 𝔹 ] ` y) [ x := true ] `` yields `` λ[ y ∶ 𝔹 ] ` y ``
* `` (λ[ x ∶ 𝔹 ] ` x) [ x := true ] `` yields `` λ[ x ∶ 𝔹 ] ` x ``

The last example is important: substituting `true` for `x` in
`` (λ[ x ∶ 𝔹 ] ` x) `` does _not_ yield `` (λ[ x ∶ 𝔹 ] true) ``.
The reason for this is that `x` in the body of `` (λ[ x ∶ 𝔹 ] ` x) ``
is _bound_ by the abstraction.  An important feature of abstraction
is that the choice of bound names is irrelevant: both
`` (λ[ x ∶ 𝔹 ] ` x) `` and `` (λ[ y ∶ 𝔹 ] ` y) `` stand for the
identity function.  The way to think of this is that `x` within
the body of the abstraction stands for a _different_ variable than
`x` outside the abstraction, they both just happen to have the same
name.

Here is the formal definition in Agda.

<pre class="Agda">{% raw %}<a id="_[_:=_]"></a><a id="12348" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">_[_:=_]</a> <a id="12356" class="Symbol">:</a> <a id="12358" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="12363" class="Symbol">→</a> <a id="12365" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2171" class="Datatype">Id</a> <a id="12368" class="Symbol">→</a> <a id="12370" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="12375" class="Symbol">→</a> <a id="12377" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a>
<a id="12382" class="Symbol">(</a><a id="12383" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="12385" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12385" class="Bound">x′</a><a id="12387" class="Symbol">)</a> <a id="12389" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">[</a> <a id="12391" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12391" class="Bound">x</a> <a id="12393" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">:=</a> <a id="12396" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12396" class="Bound">V</a> <a id="12398" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">]</a> <a id="12400" class="Keyword">with</a> <a id="12405" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12391" class="Bound">x</a> <a id="12407" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2509" class="Function Operator">≟</a> <a id="12409" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12385" class="Bound">x′</a>
<a id="12412" class="Symbol">...</a> <a id="12416" class="Symbol">|</a> <a id="12418" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#570" class="InductiveConstructor">yes</a> <a id="12422" class="Symbol">_</a> <a id="12424" class="Symbol">=</a> <a id="12426" class="Bound">V</a>
<a id="12428" class="Symbol">...</a> <a id="12432" class="Symbol">|</a> <a id="12434" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#597" class="InductiveConstructor">no</a>  <a id="12438" class="Symbol">_</a> <a id="12440" class="Symbol">=</a> <a id="12442" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="12444" class="Bound">x′</a>
<a id="12447" class="Symbol">(</a><a id="12448" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="12451" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12451" class="Bound">x′</a> <a id="12454" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="12456" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12456" class="Bound">A′</a> <a id="12459" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="12461" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12461" class="Bound">N′</a><a id="12463" class="Symbol">)</a> <a id="12465" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">[</a> <a id="12467" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12467" class="Bound">x</a> <a id="12469" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">:=</a> <a id="12472" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12472" class="Bound">V</a> <a id="12474" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">]</a> <a id="12476" class="Keyword">with</a> <a id="12481" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12467" class="Bound">x</a> <a id="12483" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2509" class="Function Operator">≟</a> <a id="12485" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12451" class="Bound">x′</a>
<a id="12488" class="Symbol">...</a> <a id="12492" class="Symbol">|</a> <a id="12494" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#570" class="InductiveConstructor">yes</a> <a id="12498" class="Symbol">_</a> <a id="12500" class="Symbol">=</a> <a id="12502" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="12505" class="Bound">x′</a> <a id="12508" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="12510" class="Bound">A′</a> <a id="12513" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="12515" class="Bound">N′</a>
<a id="12518" class="Symbol">...</a> <a id="12522" class="Symbol">|</a> <a id="12524" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#597" class="InductiveConstructor">no</a>  <a id="12528" class="Symbol">_</a> <a id="12530" class="Symbol">=</a> <a id="12532" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="12535" class="Bound">x′</a> <a id="12538" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="12540" class="Bound">A′</a> <a id="12543" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="12545" class="Symbol">(</a><a id="12546" class="Bound">N′</a> <a id="12549" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">[</a> <a id="12551" class="Bound">x</a> <a id="12553" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">:=</a> <a id="12556" class="Bound">V</a> <a id="12558" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">]</a><a id="12559" class="Symbol">)</a>
<a id="12561" class="Symbol">(</a><a id="12562" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12562" class="Bound">L′</a> <a id="12565" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="12567" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12567" class="Bound">M′</a><a id="12569" class="Symbol">)</a> <a id="12571" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">[</a> <a id="12573" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12573" class="Bound">x</a> <a id="12575" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">:=</a> <a id="12578" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12578" class="Bound">V</a> <a id="12580" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">]</a> <a id="12582" class="Symbol">=</a>  <a id="12585" class="Symbol">(</a><a id="12586" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12562" class="Bound">L′</a> <a id="12589" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">[</a> <a id="12591" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12573" class="Bound">x</a> <a id="12593" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">:=</a> <a id="12596" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12578" class="Bound">V</a> <a id="12598" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">]</a><a id="12599" class="Symbol">)</a> <a id="12601" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="12603" class="Symbol">(</a><a id="12604" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12567" class="Bound">M′</a> <a id="12607" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">[</a> <a id="12609" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12573" class="Bound">x</a> <a id="12611" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">:=</a> <a id="12614" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12578" class="Bound">V</a> <a id="12616" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">]</a><a id="12617" class="Symbol">)</a>
<a id="12619" class="Symbol">(</a><a id="12620" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a><a id="12624" class="Symbol">)</a> <a id="12626" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">[</a> <a id="12628" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12628" class="Bound">x</a> <a id="12630" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">:=</a> <a id="12633" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12633" class="Bound">V</a> <a id="12635" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">]</a> <a id="12637" class="Symbol">=</a> <a id="12639" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
<a id="12644" class="Symbol">(</a><a id="12645" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a><a id="12650" class="Symbol">)</a> <a id="12652" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">[</a> <a id="12654" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12654" class="Bound">x</a> <a id="12656" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">:=</a> <a id="12659" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12659" class="Bound">V</a> <a id="12661" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">]</a> <a id="12663" class="Symbol">=</a> <a id="12665" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a>
<a id="12671" class="Symbol">(</a><a id="12672" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="12675" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12675" class="Bound">L′</a> <a id="12678" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="12683" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12683" class="Bound">M′</a> <a id="12686" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="12691" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12691" class="Bound">N′</a><a id="12693" class="Symbol">)</a> <a id="12695" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">[</a> <a id="12697" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12697" class="Bound">x</a> <a id="12699" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">:=</a> <a id="12702" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12702" class="Bound">V</a> <a id="12704" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">]</a> <a id="12706" class="Symbol">=</a>
  <a id="12710" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="12713" class="Symbol">(</a><a id="12714" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12675" class="Bound">L′</a> <a id="12717" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">[</a> <a id="12719" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12697" class="Bound">x</a> <a id="12721" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">:=</a> <a id="12724" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12702" class="Bound">V</a> <a id="12726" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">]</a><a id="12727" class="Symbol">)</a> <a id="12729" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="12734" class="Symbol">(</a><a id="12735" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12683" class="Bound">M′</a> <a id="12738" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">[</a> <a id="12740" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12697" class="Bound">x</a> <a id="12742" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">:=</a> <a id="12745" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12702" class="Bound">V</a> <a id="12747" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">]</a><a id="12748" class="Symbol">)</a> <a id="12750" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="12755" class="Symbol">(</a><a id="12756" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12691" class="Bound">N′</a> <a id="12759" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">[</a> <a id="12761" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12697" class="Bound">x</a> <a id="12763" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">:=</a> <a id="12766" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12702" class="Bound">V</a> <a id="12768" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">]</a><a id="12769" class="Symbol">)</a>{% endraw %}</pre>

The two key cases are variables and abstraction.

* For variables, we compare `x`, the variable we are substituting for,
with `x′`, the variable in the term. If they are the same,
we yield `V`, otherwise we yield `x′` unchanged.

* For abstractions, we compare `x`, the variable we are substituting for,
with `x′`, the variable bound in the abstraction. If they are the same,
we yield abstraction unchanged, otherwise we subsititute inside the body.

In all other cases, we push substitution recursively into
the subterms.

#### Special characters

    ′  U+2032: PRIME (\')

Note that ′ (U+2032: PRIME) is not the same as ' (U+0027: APOSTROPHE).


#### Examples

Here is confirmation that the examples above are correct.

<pre class="Agda">{% raw %}<a id="ex₁₁"></a><a id="13519" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13519" class="Function">ex₁₁</a> <a id="13524" class="Symbol">:</a> <a id="13526" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13528" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="13530" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">[</a> <a id="13532" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="13534" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">:=</a> <a id="13537" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="13541" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">]</a> <a id="13543" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a>  <a id="13546" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a>
<a id="13550" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13519" class="Function">ex₁₁</a> <a id="13555" class="Symbol">=</a> <a id="13557" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="ex₁₂"></a><a id="13563" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13563" class="Function">ex₁₂</a> <a id="13568" class="Symbol">:</a> <a id="13570" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="13575" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">[</a> <a id="13577" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="13579" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">:=</a> <a id="13582" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="13586" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">]</a> <a id="13588" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13590" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
<a id="13595" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13563" class="Function">ex₁₂</a> <a id="13600" class="Symbol">=</a> <a id="13602" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="ex₁₃"></a><a id="13608" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13608" class="Function">ex₁₃</a> <a id="13613" class="Symbol">:</a> <a id="13615" class="Symbol">(</a><a id="13616" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13618" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="13620" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="13622" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a><a id="13626" class="Symbol">)</a> <a id="13628" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">[</a> <a id="13630" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="13632" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">:=</a> <a id="13635" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="13639" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">]</a> <a id="13641" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13643" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="13647" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="13649" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
<a id="13654" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13608" class="Function">ex₁₃</a> <a id="13659" class="Symbol">=</a> <a id="13661" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="ex₁₄"></a><a id="13667" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13667" class="Function">ex₁₄</a> <a id="13672" class="Symbol">:</a> <a id="13674" class="Symbol">(</a><a id="13675" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13677" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="13679" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="13681" class="Symbol">(</a><a id="13682" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13684" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="13686" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="13688" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a><a id="13692" class="Symbol">))</a> <a id="13695" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">[</a> <a id="13697" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="13699" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">:=</a> <a id="13702" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="13706" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">]</a> <a id="13708" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13710" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="13714" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="13716" class="Symbol">(</a><a id="13717" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="13721" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="13723" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a><a id="13727" class="Symbol">)</a>
<a id="13729" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13667" class="Function">ex₁₄</a> <a id="13734" class="Symbol">=</a> <a id="13736" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="ex₁₅"></a><a id="13742" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13742" class="Function">ex₁₅</a> <a id="13747" class="Symbol">:</a> <a id="13749" class="Symbol">(</a><a id="13750" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="13753" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a> <a id="13755" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="13757" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="13759" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="13761" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13763" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="13765" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="13767" class="Symbol">(</a><a id="13768" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13770" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="13772" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="13774" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13776" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a><a id="13777" class="Symbol">))</a> <a id="13780" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">[</a> <a id="13782" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">f</a> <a id="13784" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">:=</a> <a id="13787" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="13791" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">]</a> <a id="13793" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13795" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="13798" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a> <a id="13800" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="13802" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="13804" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="13806" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="13810" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="13812" class="Symbol">(</a><a id="13813" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="13817" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="13819" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13821" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a><a id="13822" class="Symbol">)</a>
<a id="13824" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13742" class="Function">ex₁₅</a> <a id="13829" class="Symbol">=</a> <a id="13831" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="ex₁₆"></a><a id="13837" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13837" class="Function">ex₁₆</a> <a id="13842" class="Symbol">:</a> <a id="13844" class="Symbol">(</a><a id="13845" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="13848" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5681" class="Function">y</a> <a id="13850" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="13852" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="13854" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="13856" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13858" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5681" class="Function">y</a><a id="13859" class="Symbol">)</a> <a id="13861" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">[</a> <a id="13863" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a> <a id="13865" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">:=</a> <a id="13868" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="13873" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">]</a> <a id="13875" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13877" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="13880" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5681" class="Function">y</a> <a id="13882" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="13884" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="13886" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="13888" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13890" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5681" class="Function">y</a>
<a id="13892" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13837" class="Function">ex₁₆</a> <a id="13897" class="Symbol">=</a> <a id="13899" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="ex₁₇"></a><a id="13905" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13905" class="Function">ex₁₇</a> <a id="13910" class="Symbol">:</a> <a id="13912" class="Symbol">(</a><a id="13913" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="13916" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a> <a id="13918" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="13920" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="13922" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="13924" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13926" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a><a id="13927" class="Symbol">)</a> <a id="13929" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">[</a> <a id="13931" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a> <a id="13933" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">:=</a> <a id="13936" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="13941" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">]</a> <a id="13943" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13945" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="13948" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a> <a id="13950" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="13952" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="13954" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="13956" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13958" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a>
<a id="13960" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13905" class="Function">ex₁₇</a> <a id="13965" class="Symbol">=</a> <a id="13967" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>

#### Quiz

What is the result of the following substitution?

    (λ[ y ∶ 𝔹 ] ` x · (λ[ x ∶ 𝔹 ] ` x)) [ x := true ]

1. `` (λ[ y ∶ 𝔹 ] ` x · (λ[ x ∶ 𝔹 ] ` x)) ``
2. `` (λ[ y ∶ 𝔹 ] ` x · (λ[ x ∶ 𝔹 ] true)) ``
3. `` (λ[ y ∶ 𝔹 ] true · (λ[ x ∶ 𝔹 ] ` x)) ``
4. `` (λ[ y ∶ 𝔹 ] true · (λ[ x ∶ 𝔹 ] ` true)) ``


## Reduction

We give the reduction rules for call-by-value lambda calculus.  To
reduce an application, first we reduce the left-hand side until it
becomes a value (which must be an abstraction); then we reduce the
right-hand side until it becomes a value; and finally we substitute
the argument for the variable in the abstraction.  To reduce a
conditional, we first reduce the condition until it becomes a value;
if the condition is true the conditional reduces to the first
branch and if false it reduces to the second branch.a

In an informal presentation of the formal semantics, 
the rules for reduction are written as follows.

    L ⟹ L′
    --------------- ξ·₁
    L · M ⟹ L′ · M

    Value V
    M ⟹ M′
    --------------- ξ·₂
    V · M ⟹ V · M′

    Value V
    --------------------------------- βλ·
    (λ[ x ∶ A ] N) · V ⟹ N [ x := V ]

    L ⟹ L′
    ----------------------------------------- ξif
    if L then M else N ⟹ if L′ then M else N

    -------------------------- βif-true
    if true then M else N ⟹ M

    --------------------------- βif-false
    if false then M else N ⟹ N

As we will show later, the rules are deterministic, in that
at most one rule applies to every term.  As we will also show
later, for every well-typed term either a reduction applies
or it is a value.

The rules break into two sorts. Compatibility rules
direct us to reduce some part of a term.
We give them names starting with the Greek letter xi, `ξ`.
Once a term is sufficiently
reduced, it will consist of a constructor and
a deconstructor, in our case `λ` and `·`, or
`if` and `true`, or `if` and `false`.
We give them names starting with the Greek letter beta, `β`,
and indeed such rules are traditionally called beta rules.

Here are the above rules formalised in Agda.

<pre class="Agda">{% raw %}<a id="16081" class="Keyword">infix</a> <a id="16087" class="Number">10</a> <a id="16090" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16101" class="Datatype Operator">_⟹_</a> 

<a id="16096" class="Keyword">data</a> <a id="_⟹_"></a><a id="16101" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16101" class="Datatype Operator">_⟹_</a> <a id="16105" class="Symbol">:</a> <a id="16107" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="16112" class="Symbol">→</a> <a id="16114" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="16119" class="Symbol">→</a> <a id="16121" class="PrimitiveType">Set</a> <a id="16125" class="Keyword">where</a>
  <a id="_⟹_.ξ·₁"></a><a id="16133" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16133" class="InductiveConstructor">ξ·₁</a> <a id="16137" class="Symbol">:</a> <a id="16139" class="Symbol">∀</a> <a id="16141" class="Symbol">{</a><a id="16142" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16142" class="Bound">L</a> <a id="16144" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16144" class="Bound">L′</a> <a id="16147" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16147" class="Bound">M</a><a id="16148" class="Symbol">}</a> <a id="16150" class="Symbol">→</a>
    <a id="16156" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16142" class="Bound">L</a> <a id="16158" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16101" class="Datatype Operator">⟹</a> <a id="16160" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16144" class="Bound">L′</a> <a id="16163" class="Symbol">→</a>
    <a id="16169" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16142" class="Bound">L</a> <a id="16171" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="16173" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16147" class="Bound">M</a> <a id="16175" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16101" class="Datatype Operator">⟹</a> <a id="16177" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16144" class="Bound">L′</a> <a id="16180" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="16182" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16147" class="Bound">M</a>
  <a id="_⟹_.ξ·₂"></a><a id="16186" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16186" class="InductiveConstructor">ξ·₂</a> <a id="16190" class="Symbol">:</a> <a id="16192" class="Symbol">∀</a> <a id="16194" class="Symbol">{</a><a id="16195" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16195" class="Bound">V</a> <a id="16197" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16197" class="Bound">M</a> <a id="16199" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16199" class="Bound">M′</a><a id="16201" class="Symbol">}</a> <a id="16203" class="Symbol">→</a>
    <a id="16209" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9722" class="Datatype">Value</a> <a id="16215" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16195" class="Bound">V</a> <a id="16217" class="Symbol">→</a>
    <a id="16223" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16197" class="Bound">M</a> <a id="16225" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16101" class="Datatype Operator">⟹</a> <a id="16227" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16199" class="Bound">M′</a> <a id="16230" class="Symbol">→</a>
    <a id="16236" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16195" class="Bound">V</a> <a id="16238" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="16240" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16197" class="Bound">M</a> <a id="16242" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16101" class="Datatype Operator">⟹</a> <a id="16244" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16195" class="Bound">V</a> <a id="16246" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="16248" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16199" class="Bound">M′</a>
  <a id="_⟹_.βλ·"></a><a id="16253" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16253" class="InductiveConstructor">βλ·</a> <a id="16257" class="Symbol">:</a> <a id="16259" class="Symbol">∀</a> <a id="16261" class="Symbol">{</a><a id="16262" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16262" class="Bound">x</a> <a id="16264" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16264" class="Bound">A</a> <a id="16266" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16266" class="Bound">N</a> <a id="16268" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16268" class="Bound">V</a><a id="16269" class="Symbol">}</a> <a id="16271" class="Symbol">→</a> <a id="16273" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9722" class="Datatype">Value</a> <a id="16279" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16268" class="Bound">V</a> <a id="16281" class="Symbol">→</a>
    <a id="16287" class="Symbol">(</a><a id="16288" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="16291" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16262" class="Bound">x</a> <a id="16293" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="16295" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16264" class="Bound">A</a> <a id="16297" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="16299" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16266" class="Bound">N</a><a id="16300" class="Symbol">)</a> <a id="16302" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="16304" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16268" class="Bound">V</a> <a id="16306" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16101" class="Datatype Operator">⟹</a> <a id="16308" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16266" class="Bound">N</a> <a id="16310" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">[</a> <a id="16312" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16262" class="Bound">x</a> <a id="16314" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">:=</a> <a id="16317" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16268" class="Bound">V</a> <a id="16319" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12348" class="Function Operator">]</a>
  <a id="_⟹_.ξif"></a><a id="16323" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16323" class="InductiveConstructor">ξif</a> <a id="16327" class="Symbol">:</a> <a id="16329" class="Symbol">∀</a> <a id="16331" class="Symbol">{</a><a id="16332" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16332" class="Bound">L</a> <a id="16334" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16334" class="Bound">L′</a> <a id="16337" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16337" class="Bound">M</a> <a id="16339" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16339" class="Bound">N</a><a id="16340" class="Symbol">}</a> <a id="16342" class="Symbol">→</a>
    <a id="16348" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16332" class="Bound">L</a> <a id="16350" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16101" class="Datatype Operator">⟹</a> <a id="16352" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16334" class="Bound">L′</a> <a id="16355" class="Symbol">→</a>    
    <a id="16365" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="16368" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16332" class="Bound">L</a> <a id="16370" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="16375" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16337" class="Bound">M</a> <a id="16377" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="16382" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16339" class="Bound">N</a> <a id="16384" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16101" class="Datatype Operator">⟹</a> <a id="16386" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="16389" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16334" class="Bound">L′</a> <a id="16392" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="16397" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16337" class="Bound">M</a> <a id="16399" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="16404" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16339" class="Bound">N</a>
  <a id="_⟹_.βif-true"></a><a id="16408" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16408" class="InductiveConstructor">βif-true</a> <a id="16417" class="Symbol">:</a> <a id="16419" class="Symbol">∀</a> <a id="16421" class="Symbol">{</a><a id="16422" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16422" class="Bound">M</a> <a id="16424" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16424" class="Bound">N</a><a id="16425" class="Symbol">}</a> <a id="16427" class="Symbol">→</a>
    <a id="16433" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="16436" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="16441" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="16446" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16422" class="Bound">M</a> <a id="16448" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="16453" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16424" class="Bound">N</a> <a id="16455" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16101" class="Datatype Operator">⟹</a> <a id="16457" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16422" class="Bound">M</a>
  <a id="_⟹_.βif-false"></a><a id="16461" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16461" class="InductiveConstructor">βif-false</a> <a id="16471" class="Symbol">:</a> <a id="16473" class="Symbol">∀</a> <a id="16475" class="Symbol">{</a><a id="16476" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16476" class="Bound">M</a> <a id="16478" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16478" class="Bound">N</a><a id="16479" class="Symbol">}</a> <a id="16481" class="Symbol">→</a>
    <a id="16487" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="16490" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a> <a id="16496" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="16501" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16476" class="Bound">M</a> <a id="16503" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="16508" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16478" class="Bound">N</a> <a id="16510" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16101" class="Datatype Operator">⟹</a> <a id="16512" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16478" class="Bound">N</a>{% endraw %}</pre>

#### Special characters

We use the following special characters

    ⟹  U+27F9: LONG RIGHTWARDS DOUBLE ARROW (\r6)
    ξ  U+03BE: GREEK SMALL LETTER XI (\Gx or \xi)
    β  U+03B2: GREEK SMALL LETTER BETA (\Gb or \beta)

#### Quiz

What does the following term step to?

    (λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) · (λ [ x ∶ 𝔹 ] ` x)  ⟹  ???

1.  `` (λ [ x ∶ 𝔹 ] ` x) ``
2.  `` (λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) ``
3.  `` (λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) · (λ [ x ∶ 𝔹 ] ` x) ``

What does the following term step to?

    (λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) · ((λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) (λ [ x ∶ 𝔹 ] ` x))  ⟹  ???

1.  `` (λ [ x ∶ 𝔹 ] ` x) ``
2.  `` (λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) ``
3.  `` (λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) · (λ [ x ∶ 𝔹 ] ` x) ``

What does the following term step to?  (Where `not` is as defined above.)

    not · true  ⟹  ???

1.  `` if ` x then false else true ``
2.  `` if true then false else true ``
3.  `` true ``
4.  `` false ``

What does the following term step to?  (Where `two` and `not` are as defined above.)

    two · not · true  ⟹  ???

1.  `` not · (not · true) ``
2.  `` (λ[ x ∶ 𝔹 ] not · (not · ` x)) · true ``
4.  `` true ``
5.  `` false ``

## Reflexive and transitive closure

A single step is only part of the story. In general, we wish to repeatedly
step a closed term until it reduces to a value.  We do this by defining
the reflexive and transitive closure `⟹*` of the step function `⟹`.
In an informal presentation of the formal semantics, the rules
are written as follows.

    ------- done
    M ⟹* M

    L ⟹ M
    M ⟹* N
    ------- step
    L ⟹* N

Here it is formalised in Agda.

<pre class="Agda">{% raw %}<a id="18086" class="Keyword">infix</a> <a id="18092" class="Number">10</a> <a id="18095" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18135" class="Datatype Operator">_⟹*_</a> 
<a id="18101" class="Keyword">infixr</a> <a id="18108" class="Number">2</a> <a id="18110" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18188" class="InductiveConstructor Operator">_⟹⟨_⟩_</a>
<a id="18117" class="Keyword">infix</a>  <a id="18124" class="Number">3</a> <a id="18126" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18168" class="InductiveConstructor Operator">_∎</a>

<a id="18130" class="Keyword">data</a> <a id="_⟹*_"></a><a id="18135" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18135" class="Datatype Operator">_⟹*_</a> <a id="18140" class="Symbol">:</a> <a id="18142" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="18147" class="Symbol">→</a> <a id="18149" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="18154" class="Symbol">→</a> <a id="18156" class="PrimitiveType">Set</a> <a id="18160" class="Keyword">where</a>
  <a id="_⟹*_._∎"></a><a id="18168" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18168" class="InductiveConstructor Operator">_∎</a> <a id="18171" class="Symbol">:</a> <a id="18173" class="Symbol">∀</a> <a id="18175" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18175" class="Bound">M</a> <a id="18177" class="Symbol">→</a> <a id="18179" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18175" class="Bound">M</a> <a id="18181" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18135" class="Datatype Operator">⟹*</a> <a id="18184" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18175" class="Bound">M</a>
  <a id="_⟹*_._⟹⟨_⟩_"></a><a id="18188" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18188" class="InductiveConstructor Operator">_⟹⟨_⟩_</a> <a id="18195" class="Symbol">:</a> <a id="18197" class="Symbol">∀</a> <a id="18199" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18199" class="Bound">L</a> <a id="18201" class="Symbol">{</a><a id="18202" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18202" class="Bound">M</a> <a id="18204" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18204" class="Bound">N</a><a id="18205" class="Symbol">}</a> <a id="18207" class="Symbol">→</a> <a id="18209" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18199" class="Bound">L</a> <a id="18211" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16101" class="Datatype Operator">⟹</a> <a id="18213" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18202" class="Bound">M</a> <a id="18215" class="Symbol">→</a> <a id="18217" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18202" class="Bound">M</a> <a id="18219" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18135" class="Datatype Operator">⟹*</a> <a id="18222" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18204" class="Bound">N</a> <a id="18224" class="Symbol">→</a> <a id="18226" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18199" class="Bound">L</a> <a id="18228" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18135" class="Datatype Operator">⟹*</a> <a id="18231" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18204" class="Bound">N</a>{% endraw %}</pre>

We can read this as follows.

* From term `M`, we can take no steps, giving `M ∎` of type `M ⟹* M`.

* From term `L` we can take a single step `L⟹M` of type `L ⟹ M`
  followed by zero or more steps `M⟹*N` of type `M ⟹* N`,
  giving `L ⟨ L⟹M ⟩ M⟹*N` of type `L ⟹* N`.

The names of the two clauses in the definition of reflexive
and transitive closure have been chosen to allow us to lay
out example reductions in an appealing way.

<pre class="Agda">{% raw %}<a id="reduction₁"></a><a id="18692" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18692" class="Function">reduction₁</a> <a id="18703" class="Symbol">:</a> <a id="18705" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="18709" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="18711" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="18716" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18135" class="Datatype Operator">⟹*</a> <a id="18719" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a>
<a id="18725" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18692" class="Function">reduction₁</a> <a id="18736" class="Symbol">=</a>
    <a id="18742" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="18746" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="18748" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
  <a id="18755" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18188" class="InductiveConstructor Operator">⟹⟨</a> <a id="18758" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16253" class="InductiveConstructor">βλ·</a> <a id="18762" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9798" class="InductiveConstructor">value-true</a> <a id="18773" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18188" class="InductiveConstructor Operator">⟩</a>
    <a id="18779" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="18782" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="18787" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="18792" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a> <a id="18798" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="18803" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
  <a id="18810" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18188" class="InductiveConstructor Operator">⟹⟨</a> <a id="18813" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16408" class="InductiveConstructor">βif-true</a> <a id="18822" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18188" class="InductiveConstructor Operator">⟩</a>
    <a id="18828" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a>
  <a id="18836" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18168" class="InductiveConstructor Operator">∎</a>

<a id="reduction₂"></a><a id="18839" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18839" class="Function">reduction₂</a> <a id="18850" class="Symbol">:</a> <a id="18852" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5726" class="Function">two</a> <a id="18856" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="18858" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="18862" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="18864" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="18869" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18135" class="Datatype Operator">⟹*</a> <a id="18872" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
<a id="18877" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18839" class="Function">reduction₂</a> <a id="18888" class="Symbol">=</a>
    <a id="18894" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5726" class="Function">two</a> <a id="18898" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="18900" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="18904" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="18906" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
  <a id="18913" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18188" class="InductiveConstructor Operator">⟹⟨</a> <a id="18916" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16133" class="InductiveConstructor">ξ·₁</a> <a id="18920" class="Symbol">(</a><a id="18921" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16253" class="InductiveConstructor">βλ·</a> <a id="18925" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9749" class="InductiveConstructor">value-λ</a><a id="18932" class="Symbol">)</a> <a id="18934" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18188" class="InductiveConstructor Operator">⟩</a>
    <a id="18940" class="Symbol">(</a><a id="18941" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="18944" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a> <a id="18946" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="18948" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="18950" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="18952" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="18956" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="18958" class="Symbol">(</a><a id="18959" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="18963" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="18965" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="18967" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a><a id="18968" class="Symbol">))</a> <a id="18971" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="18973" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
  <a id="18980" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18188" class="InductiveConstructor Operator">⟹⟨</a> <a id="18983" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16253" class="InductiveConstructor">βλ·</a> <a id="18987" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9798" class="InductiveConstructor">value-true</a> <a id="18998" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18188" class="InductiveConstructor Operator">⟩</a>
    <a id="19004" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="19008" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="19010" class="Symbol">(</a><a id="19011" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="19015" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="19017" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a><a id="19021" class="Symbol">)</a>
  <a id="19025" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18188" class="InductiveConstructor Operator">⟹⟨</a> <a id="19028" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16186" class="InductiveConstructor">ξ·₂</a> <a id="19032" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9749" class="InductiveConstructor">value-λ</a> <a id="19040" class="Symbol">(</a><a id="19041" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16253" class="InductiveConstructor">βλ·</a> <a id="19045" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9798" class="InductiveConstructor">value-true</a><a id="19055" class="Symbol">)</a> <a id="19057" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18188" class="InductiveConstructor Operator">⟩</a>
    <a id="19063" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="19067" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="19069" class="Symbol">(</a><a id="19070" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="19073" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="19078" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="19083" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a> <a id="19089" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="19094" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a><a id="19098" class="Symbol">)</a>
  <a id="19102" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18188" class="InductiveConstructor Operator">⟹⟨</a> <a id="19105" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16186" class="InductiveConstructor">ξ·₂</a> <a id="19109" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9749" class="InductiveConstructor">value-λ</a> <a id="19117" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16408" class="InductiveConstructor">βif-true</a>  <a id="19127" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18188" class="InductiveConstructor Operator">⟩</a>
    <a id="19133" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="19137" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="19139" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a>
  <a id="19147" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18188" class="InductiveConstructor Operator">⟹⟨</a> <a id="19150" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16253" class="InductiveConstructor">βλ·</a> <a id="19154" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9825" class="InductiveConstructor">value-false</a> <a id="19166" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18188" class="InductiveConstructor Operator">⟩</a>
    <a id="19172" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="19175" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a> <a id="19181" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="19186" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a> <a id="19192" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="19197" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
  <a id="19204" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18188" class="InductiveConstructor Operator">⟹⟨</a> <a id="19207" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16461" class="InductiveConstructor">βif-false</a> <a id="19217" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18188" class="InductiveConstructor Operator">⟩</a>
    <a id="19223" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
  <a id="19230" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18168" class="InductiveConstructor Operator">∎</a>{% endraw %}</pre>

Much of the above, though not all, can be filled in using C-c C-r and C-c C-s.

#### Special characters

We use the following special characters

    ∎  U+220E: END OF PROOF (\qed)
    ⟨  U+27E8: MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9: MATHEMATICAL RIGHT ANGLE BRACKET (\>)

## Typing

While reduction considers only closed terms, typing must
consider terms with free variables.  To type a term,
we must first type its subterms, and in particular in the
body of an abstraction its bound variable may appear free.

In general, we use typing _judgements_ of the form

    Γ ⊢ M ∶ A

which asserts in type environment `Γ` that term `M` has type `A`.
Environment `Γ` provides types for all the free variables in `M`.

Here are three examples. 

* `` ∅ , f ∶ 𝔹 ⇒ 𝔹 , x ∶ 𝔹 ⊢ ` f · (` f · ` x) ∶  𝔹 ``
* `` ∅ , f ∶ 𝔹 ⇒ 𝔹 ⊢ (λ[ x ∶ 𝔹 ] ` f · (` f · ` x)) ∶  𝔹 ⇒ 𝔹 ``
* `` ∅ ⊢ (λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x)) ∶  (𝔹 ⇒ 𝔹) ⇒ 𝔹 ⇒ 𝔹 ``

Environments are partial maps from identifiers to types, built using `∅`
for the empty map, and `Γ , x ∶ A` for the map that extends
environment `Γ` by mapping variable `x` to type `A`.

In an informal presentation of the formal semantics, 
the rules for typing are written as follows.

    Γ x ≡ A
    ----------- Ax
    Γ ⊢ ` x ∶ A

    Γ , x ∶ A ⊢ N ∶ B
    ------------------------ ⇒-I
    Γ ⊢ λ[ x ∶ A ] N ∶ A ⇒ B

    Γ ⊢ L ∶ A ⇒ B
    Γ ⊢ M ∶ A
    -------------- ⇒-E
    Γ ⊢ L · M ∶ B

    ------------- 𝔹-I₁
    Γ ⊢ true ∶ 𝔹

    -------------- 𝔹-I₂
    Γ ⊢ false ∶ 𝔹

    Γ ⊢ L : 𝔹
    Γ ⊢ M ∶ A
    Γ ⊢ N ∶ A
    -------------------------- 𝔹-E
    Γ ⊢ if L then M else N ∶ A

As we will show later, the rules are deterministic, in that
at most one rule applies to every term. 

The proof rules come in pairs, with rules to introduce and to
eliminate each connective, labeled `-I` and `-E`, respectively. As we
read the rules from top to bottom, introduction and elimination rules
do what they say on the tin: the first _introduces_ a formula for the
connective, which appears in the conclusion but not in the premises;
while the second _eliminates_ a formula for the connective, which appears in
a premise but not in the conclusion. An introduction rule describes
how to construct a value of the type (abstractions yield functions,
true and false yield booleans), while an elimination rule describes
how to deconstruct a value of the given type (applications use
functions, conditionals use booleans).

Here are the above rules formalised in Agda.

<pre class="Agda">{% raw %}<a id="Context"></a><a id="21767" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21767" class="Function">Context</a> <a id="21775" class="Symbol">:</a> <a id="21777" class="PrimitiveType">Set</a>
<a id="21781" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21767" class="Function">Context</a> <a id="21789" class="Symbol">=</a> <a id="21791" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10132" class="Function">PartialMap</a> <a id="21802" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2564" class="Datatype">Type</a>

<a id="21808" class="Keyword">infix</a> <a id="21814" class="Number">10</a> <a id="21817" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">_⊢_∶_</a>

<a id="21824" class="Keyword">data</a> <a id="_⊢_∶_"></a><a id="21829" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">_⊢_∶_</a> <a id="21835" class="Symbol">:</a> <a id="21837" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21767" class="Function">Context</a> <a id="21845" class="Symbol">→</a> <a id="21847" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="21852" class="Symbol">→</a> <a id="21854" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2564" class="Datatype">Type</a> <a id="21859" class="Symbol">→</a> <a id="21861" class="PrimitiveType">Set</a> <a id="21865" class="Keyword">where</a>
  <a id="_⊢_∶_.Ax"></a><a id="21873" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21873" class="InductiveConstructor">Ax</a> <a id="21876" class="Symbol">:</a> <a id="21878" class="Symbol">∀</a> <a id="21880" class="Symbol">{</a><a id="21881" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21881" class="Bound">Γ</a> <a id="21883" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21883" class="Bound">x</a> <a id="21885" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21885" class="Bound">A</a><a id="21886" class="Symbol">}</a> <a id="21888" class="Symbol">→</a>
    <a id="21894" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21881" class="Bound">Γ</a> <a id="21896" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21883" class="Bound">x</a> <a id="21898" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="21900" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor">just</a> <a id="21905" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21885" class="Bound">A</a> <a id="21907" class="Symbol">→</a>
    <a id="21913" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21881" class="Bound">Γ</a> <a id="21915" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">⊢</a> <a id="21917" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="21919" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21883" class="Bound">x</a> <a id="21921" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">∶</a> <a id="21923" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21885" class="Bound">A</a>
  <a id="_⊢_∶_.⇒-I"></a><a id="21927" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21927" class="InductiveConstructor">⇒-I</a> <a id="21931" class="Symbol">:</a> <a id="21933" class="Symbol">∀</a> <a id="21935" class="Symbol">{</a><a id="21936" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21936" class="Bound">Γ</a> <a id="21938" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21938" class="Bound">x</a> <a id="21940" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21940" class="Bound">N</a> <a id="21942" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21942" class="Bound">A</a> <a id="21944" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21944" class="Bound">B</a><a id="21945" class="Symbol">}</a> <a id="21947" class="Symbol">→</a>
    <a id="21953" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21936" class="Bound">Γ</a> <a id="21955" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10368" class="Function Operator">,</a> <a id="21957" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21938" class="Bound">x</a> <a id="21959" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10368" class="Function Operator">∶</a> <a id="21961" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21942" class="Bound">A</a> <a id="21963" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">⊢</a> <a id="21965" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21940" class="Bound">N</a> <a id="21967" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">∶</a> <a id="21969" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21944" class="Bound">B</a> <a id="21971" class="Symbol">→</a>
    <a id="21977" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21936" class="Bound">Γ</a> <a id="21979" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">⊢</a> <a id="21981" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="21984" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21938" class="Bound">x</a> <a id="21986" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="21988" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21942" class="Bound">A</a> <a id="21990" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="21992" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21940" class="Bound">N</a> <a id="21994" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">∶</a> <a id="21996" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21942" class="Bound">A</a> <a id="21998" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="22000" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21944" class="Bound">B</a>
  <a id="_⊢_∶_.⇒-E"></a><a id="22004" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22004" class="InductiveConstructor">⇒-E</a> <a id="22008" class="Symbol">:</a> <a id="22010" class="Symbol">∀</a> <a id="22012" class="Symbol">{</a><a id="22013" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22013" class="Bound">Γ</a> <a id="22015" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22015" class="Bound">L</a> <a id="22017" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22017" class="Bound">M</a> <a id="22019" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22019" class="Bound">A</a> <a id="22021" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22021" class="Bound">B</a><a id="22022" class="Symbol">}</a> <a id="22024" class="Symbol">→</a>
    <a id="22030" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22013" class="Bound">Γ</a> <a id="22032" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">⊢</a> <a id="22034" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22015" class="Bound">L</a> <a id="22036" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">∶</a> <a id="22038" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22019" class="Bound">A</a> <a id="22040" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="22042" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22021" class="Bound">B</a> <a id="22044" class="Symbol">→</a>
    <a id="22050" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22013" class="Bound">Γ</a> <a id="22052" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">⊢</a> <a id="22054" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22017" class="Bound">M</a> <a id="22056" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">∶</a> <a id="22058" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22019" class="Bound">A</a> <a id="22060" class="Symbol">→</a>
    <a id="22066" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22013" class="Bound">Γ</a> <a id="22068" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">⊢</a> <a id="22070" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22015" class="Bound">L</a> <a id="22072" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="22074" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22017" class="Bound">M</a> <a id="22076" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">∶</a> <a id="22078" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22021" class="Bound">B</a>
  <a id="_⊢_∶_.𝔹-I₁"></a><a id="22082" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22082" class="InductiveConstructor">𝔹-I₁</a> <a id="22087" class="Symbol">:</a> <a id="22089" class="Symbol">∀</a> <a id="22091" class="Symbol">{</a><a id="22092" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22092" class="Bound">Γ</a><a id="22093" class="Symbol">}</a> <a id="22095" class="Symbol">→</a>
    <a id="22101" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22092" class="Bound">Γ</a> <a id="22103" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">⊢</a> <a id="22105" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="22110" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">∶</a> <a id="22112" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a>
  <a id="_⊢_∶_.𝔹-I₂"></a><a id="22116" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22116" class="InductiveConstructor">𝔹-I₂</a> <a id="22121" class="Symbol">:</a> <a id="22123" class="Symbol">∀</a> <a id="22125" class="Symbol">{</a><a id="22126" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22126" class="Bound">Γ</a><a id="22127" class="Symbol">}</a> <a id="22129" class="Symbol">→</a>
    <a id="22135" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22126" class="Bound">Γ</a> <a id="22137" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">⊢</a> <a id="22139" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a> <a id="22145" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">∶</a> <a id="22147" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a>
  <a id="_⊢_∶_.𝔹-E"></a><a id="22151" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22151" class="InductiveConstructor">𝔹-E</a> <a id="22155" class="Symbol">:</a> <a id="22157" class="Symbol">∀</a> <a id="22159" class="Symbol">{</a><a id="22160" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22160" class="Bound">Γ</a> <a id="22162" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22162" class="Bound">L</a> <a id="22164" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22164" class="Bound">M</a> <a id="22166" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22166" class="Bound">N</a> <a id="22168" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22168" class="Bound">A</a><a id="22169" class="Symbol">}</a> <a id="22171" class="Symbol">→</a>
    <a id="22177" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22160" class="Bound">Γ</a> <a id="22179" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">⊢</a> <a id="22181" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22162" class="Bound">L</a> <a id="22183" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">∶</a> <a id="22185" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="22187" class="Symbol">→</a>
    <a id="22193" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22160" class="Bound">Γ</a> <a id="22195" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">⊢</a> <a id="22197" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22164" class="Bound">M</a> <a id="22199" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">∶</a> <a id="22201" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22168" class="Bound">A</a> <a id="22203" class="Symbol">→</a>
    <a id="22209" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22160" class="Bound">Γ</a> <a id="22211" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">⊢</a> <a id="22213" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22166" class="Bound">N</a> <a id="22215" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">∶</a> <a id="22217" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22168" class="Bound">A</a> <a id="22219" class="Symbol">→</a>
    <a id="22225" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22160" class="Bound">Γ</a> <a id="22227" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">⊢</a> <a id="22229" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="22232" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22162" class="Bound">L</a> <a id="22234" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="22239" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22164" class="Bound">M</a> <a id="22241" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="22246" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22166" class="Bound">N</a> <a id="22248" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">∶</a> <a id="22250" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22168" class="Bound">A</a>{% endraw %}</pre>

#### Example type derivations

Here are a couple of typing examples.  First, here is how
they would be written in an informal description of the
formal semantics.

Derivation of `not`:

    ------------ Ax    ------------- 𝔹-I₂    ------------- 𝔹-I₁
    Γ₀ ⊢ ` x ∶ 𝔹       Γ₀ ⊢ false ∶ 𝔹         Γ₀ ⊢ true ∶ 𝔹
    ------------------------------------------------------ 𝔹-E
    Γ₀ ⊢ if ` x then false else true ∶ 𝔹
    --------------------------------------------------- ⇒-I
    ∅ ⊢ λ[ x ∶ 𝔹 ] if ` x then false else true ∶ 𝔹 ⇒ 𝔹

where `Γ₀ = ∅ , x ∶ 𝔹`.

Derivation of `two`:

                            ----------------- Ax     ------------ Ax
                            Γ₂ ⊢ ` f ∶ 𝔹 ⇒ 𝔹         Γ₂ ⊢ ` x ∶ 𝔹
    ----------------- Ax    ------------------------------------- ⇒-E
    Γ₂ ⊢ ` f ∶ 𝔹 ⇒ 𝔹        Γ₂ ⊢ ` f · ` x ∶ 𝔹
    -------------------------------------------  ⇒-E
    Γ₂ ⊢ ` f · (` f · ` x) ∶ 𝔹
    ------------------------------------------ ⇒-I
    Γ₁ ⊢ λ[ x ∶ 𝔹 ] ` f · (` f · ` x) ∶ 𝔹 ⇒ 𝔹
    ---------------------------------------------------------- ⇒-I
    ∅ ⊢ λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x) ∶ 𝔹 ⇒ 𝔹

where `Γ₁ = ∅ , f ∶ 𝔹 ⇒ 𝔹` and `Γ₂ = ∅ , f ∶ 𝔹 ⇒ 𝔹 , x ∶ 𝔹`.

Here are the above derivations formalised in Agda.

<pre class="Agda">{% raw %}<a id="typing₁"></a><a id="23533" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#23533" class="Function">typing₁</a> <a id="23541" class="Symbol">:</a> <a id="23543" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10265" class="Function">∅</a> <a id="23545" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">⊢</a> <a id="23547" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5722" class="Function">not</a> <a id="23551" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">∶</a> <a id="23553" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="23555" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="23557" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a>
<a id="23559" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#23533" class="Function">typing₁</a> <a id="23567" class="Symbol">=</a> <a id="23569" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21927" class="InductiveConstructor">⇒-I</a> <a id="23573" class="Symbol">(</a><a id="23574" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22151" class="InductiveConstructor">𝔹-E</a> <a id="23578" class="Symbol">(</a><a id="23579" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21873" class="InductiveConstructor">Ax</a> <a id="23582" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="23586" class="Symbol">)</a> <a id="23588" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22116" class="InductiveConstructor">𝔹-I₂</a> <a id="23593" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22082" class="InductiveConstructor">𝔹-I₁</a><a id="23597" class="Symbol">)</a>

<a id="typing₂"></a><a id="23600" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#23600" class="Function">typing₂</a> <a id="23608" class="Symbol">:</a> <a id="23610" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10265" class="Function">∅</a> <a id="23612" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">⊢</a> <a id="23614" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5726" class="Function">two</a> <a id="23618" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">∶</a> <a id="23620" class="Symbol">(</a><a id="23621" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="23623" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="23625" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a><a id="23626" class="Symbol">)</a> <a id="23628" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="23630" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="23632" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="23634" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a>
<a id="23636" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#23600" class="Function">typing₂</a> <a id="23644" class="Symbol">=</a> <a id="23646" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21927" class="InductiveConstructor">⇒-I</a> <a id="23650" class="Symbol">(</a><a id="23651" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21927" class="InductiveConstructor">⇒-I</a> <a id="23655" class="Symbol">(</a><a id="23656" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22004" class="InductiveConstructor">⇒-E</a> <a id="23660" class="Symbol">(</a><a id="23661" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21873" class="InductiveConstructor">Ax</a> <a id="23664" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="23668" class="Symbol">)</a> <a id="23670" class="Symbol">(</a><a id="23671" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22004" class="InductiveConstructor">⇒-E</a> <a id="23675" class="Symbol">(</a><a id="23676" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21873" class="InductiveConstructor">Ax</a> <a id="23679" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="23683" class="Symbol">)</a> <a id="23685" class="Symbol">(</a><a id="23686" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21873" class="InductiveConstructor">Ax</a> <a id="23689" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="23693" class="Symbol">))))</a>{% endraw %}</pre>

#### Interaction with Agda

Construction of a type derivation is best done interactively.
Start with the declaration:

    typing₁ : ∅ ⊢ not ∶ 𝔹 ⇒ 𝔹
    typing₁ = ?

Typing C-l causes Agda to create a hole and tell us its expected type.

    typing₁ = { }0
    ?0 : ∅ ⊢ not ∶ 𝔹 ⇒ 𝔹

Now we fill in the hole by typing C-c C-r. Agda observes that
the outermost term in `not` in a `λ`, which is typed using `⇒-I`. The
`⇒-I` rule in turn takes one argument, which Agda leaves as a hole.

    typing₁ = ⇒-I { }0
    ?0 : ∅ , x ∶ 𝔹 ⊢ if ` x then false else true ∶ 𝔹

Again we fill in the hole by typing C-c C-r. Agda observes that the
outermost term is now `if_then_else_`, which is typed using `𝔹-E`. The
`𝔹-E` rule in turn takes three arguments, which Agda leaves as holes.

    typing₁ = ⇒-I (𝔹-E { }0 { }1 { }2)
    ?0 : ∅ , x ∶ 𝔹 ⊢ ` x ∶
    ?1 : ∅ , x ∶ 𝔹 ⊢ false ∶ 𝔹
    ?2 : ∅ , x ∶ 𝔹 ⊢ true ∶ 𝔹

Again we fill in the three holes by typing C-c C-r in each. Agda observes
that `` ` x ``, `false`, and `true` are typed using `Ax`, `𝔹-I₂`, and
`𝔹-I₁` respectively. The `Ax` rule in turn takes an argument, to show
that `(∅ , x ∶ 𝔹) x = just 𝔹`, which can in turn be specified with a
hole. After filling in all holes, the term is as above.

The entire process can be automated using Agsy, invoked with C-c C-a.

#### Non-examples

We can also show that terms are _not_ typeable.  For example, here is
a formal proof that it is not possible to type the term `` true ·
false ``.  In other words, no type `A` is the type of this term.  It
cannot be typed, because doing so requires that the first term in the
application is both a boolean and a function.

<pre class="Agda">{% raw %}<a id="notyping₂"></a><a id="25374" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25374" class="Function">notyping₂</a> <a id="25384" class="Symbol">:</a> <a id="25386" class="Symbol">∀</a> <a id="25388" class="Symbol">{</a><a id="25389" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25389" class="Bound">A</a><a id="25390" class="Symbol">}</a> <a id="25392" class="Symbol">→</a> <a id="25394" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#464" class="Function Operator">¬</a> <a id="25396" class="Symbol">(</a><a id="25397" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10265" class="Function">∅</a> <a id="25399" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">⊢</a> <a id="25401" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="25406" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="25408" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a> <a id="25414" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">∶</a> <a id="25416" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25389" class="Bound">A</a><a id="25417" class="Symbol">)</a>
<a id="25419" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25374" class="Function">notyping₂</a> <a id="25429" class="Symbol">(</a><a id="25430" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22004" class="InductiveConstructor">⇒-E</a> <a id="25434" class="Symbol">()</a> <a id="25437" class="Symbol">_)</a>{% endraw %}</pre>

As a second example, here is a formal proof that it is not possible to
type `` λ[ x ∶ 𝔹 ] λ[ y ∶ 𝔹 ] ` x · ` y `` It cannot be typed, because
doing so requires `x` to be both boolean and a function.

<pre class="Agda">{% raw %}<a id="contradiction"></a><a id="25665" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25665" class="Function">contradiction</a> <a id="25679" class="Symbol">:</a> <a id="25681" class="Symbol">∀</a> <a id="25683" class="Symbol">{</a><a id="25684" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25684" class="Bound">A</a> <a id="25686" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25686" class="Bound">B</a><a id="25687" class="Symbol">}</a> <a id="25689" class="Symbol">→</a> <a id="25691" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#464" class="Function Operator">¬</a> <a id="25693" class="Symbol">(</a><a id="25694" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="25696" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="25698" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25684" class="Bound">A</a> <a id="25700" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="25702" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25686" class="Bound">B</a><a id="25703" class="Symbol">)</a>
<a id="25705" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25665" class="Function">contradiction</a> <a id="25719" class="Symbol">()</a>

<a id="notyping₁"></a><a id="25723" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25723" class="Function">notyping₁</a> <a id="25733" class="Symbol">:</a> <a id="25735" class="Symbol">∀</a> <a id="25737" class="Symbol">{</a><a id="25738" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25738" class="Bound">A</a><a id="25739" class="Symbol">}</a> <a id="25741" class="Symbol">→</a> <a id="25743" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#464" class="Function Operator">¬</a> <a id="25745" class="Symbol">(</a><a id="25746" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10265" class="Function">∅</a> <a id="25748" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">⊢</a> <a id="25750" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="25753" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a> <a id="25755" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="25757" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="25759" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="25761" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="25764" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5681" class="Function">y</a> <a id="25766" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="25768" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="25770" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="25772" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="25774" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">x</a> <a id="25776" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="25778" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="25780" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5681" class="Function">y</a> <a id="25782" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21829" class="Datatype Operator">∶</a> <a id="25784" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25738" class="Bound">A</a><a id="25785" class="Symbol">)</a>
<a id="25787" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25723" class="Function">notyping₁</a> <a id="25797" class="Symbol">(</a><a id="25798" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21927" class="InductiveConstructor">⇒-I</a> <a id="25802" class="Symbol">(</a><a id="25803" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21927" class="InductiveConstructor">⇒-I</a> <a id="25807" class="Symbol">(</a><a id="25808" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22004" class="InductiveConstructor">⇒-E</a> <a id="25812" class="Symbol">(</a><a id="25813" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21873" class="InductiveConstructor">Ax</a> <a id="25816" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25816" class="Bound">Γx</a><a id="25818" class="Symbol">)</a> <a id="25820" class="Symbol">_)))</a> <a id="25825" class="Symbol">=</a>  <a id="25828" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25665" class="Function">contradiction</a> <a id="25842" class="Symbol">(</a><a id="25843" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#11919" class="Function">just-injective</a> <a id="25858" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25816" class="Bound">Γx</a><a id="25860" class="Symbol">)</a>{% endraw %}</pre>


#### Quiz

For each of the following, given a type `A` for which it is derivable,
or explain why there is no such `A`.

1. `` ∅ , y ∶ A ⊢ λ[ x ∶ 𝔹 ] ` x ∶ 𝔹 ⇒ 𝔹 ``
2. `` ∅ ⊢ λ[ y ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` y · ` x ∶ A ``
3. `` ∅ ⊢ λ[ y ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` x · ` y ∶ A ``
4. `` ∅ , x ∶ A ⊢ λ[ y : 𝔹 ⇒ 𝔹 ] `y · `x : A ``

For each of the following, give type `A`, `B`, `C`, and `D` for which it is derivable,
or explain why there are no such types.

1. `` ∅ ⊢ λ[ y ∶ 𝔹 ⇒ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` y · ` x ∶ A ``
2. `` ∅ , x ∶ A ⊢ x · x ∶ B ``
3. `` ∅ , x ∶ A , y ∶ B ⊢ λ[ z ∶ C ] ` x · (` y · ` z) ∶ D ``



