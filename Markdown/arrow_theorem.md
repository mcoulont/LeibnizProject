---
title: "Arrow's theorem"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - social choice
...


## Presentation

Here is what's probably the most famous result in voting theory: [Arrow's impossibility theorem.](https://en.wikipedia.org/wiki/Arrow's_impossibility_theorem)

Let's say that at least 3 candidates compete at an election. Each voter has a preference order (possibly with ties) on the candidates. We wish some kind of a recipe (a general one, used at each election) to sum up all these preference orders into a single one (called social preference). Then it is quite natural to require that:\
- if every one prefers a candidate to another, then so does the social preference\
- there is no one whose vote determines alone the social preference (regardless of the votes of other individuals)\
- the social preference between two candidates only depends on the individual preferences between them. Thus, if a candidate withdraws, this doesn't change the social preference between the other candidates.\
Arrow's theorem states that such a recipe doesn't exist.

We follow below [this Lean 3 proof](https://github.com/asouther4/lean-social-choice/blob/master/src/arrows_theorem.lean), which is itself based on the first of the 3 proofs in [this article](http://dido.econ.yale.edu/~gean/art/p1116.pdf).

--MATH_START--
Throughout this page, let $I$ the finite set of individuals (voters) of a society and $A$ be the set of alternatives (candidates).

$\mathbf{Definition}$\
A preference order is a reflexive and total relation on $A$. \
Let $O$ be the set of preference orders on $A$. \
We denote $a \prec_i b$ the fact that individual $i$ strictly prefers $b$ over $a$ and $a \succeq_i b$ the fact that individual $i$ (possibly equally) prefers $a$ over $b$. \
If $a \preceq_i b$ and $b \preceq_i a$, $a$ and $b$ are said indifferent.
--MATH_END--

[//]: # Coq (2-18)


## Fundamental definitions

A preference profile is a collection of preference orders on candidates (one for each individual/voter).

--MATH_START--
$\mathbf{Definition}$\
A preference profile is a function from $I$ to $O$.\
Let $P$ be the set of preference profiles.\
We denote $a \succ_p b$ (or just $a \succ b$ if there is no ambiguity) the fact that the society (whose individual preferences are described with the preference profile $p$) strictly prefers $a$ over $b$ and $a \preceq_p b$ the fact that the society (possibly equally) prefers $b$ over $a$.
--MATH_END--

[//]: # Coq (20-20)

A constitution is a way to aggregate all the individual preference orders into a single one.

--MATH_START--
$\mathbf{Definition}$\
A constitution is a function from $P$ to $O$.
--MATH_END--

[//]: # Coq (22-22)

A preference profile unanimously (strictly) prefers an alternative over another one if every individual does so.

--MATH_START--
$\mathbf{Definition}$\
A preference profile is unanimously prefer an alternative $a$ over another alternative $b$ if $\forall i \in I, a \succ_i b$.
--MATH_END--

[//]: # Coq (24-25)

A constitution is said to respect unanimity if it prefers a candidate to another when every individual does so.

--MATH_START--
$\mathbf{Definition}$\
A constitution respects unanimity if
$$\forall p \in P, a,b \in A, p \text{ unanimously prefers } a \text{ over } b \Rightarrow a \succ_p b$$
--MATH_END--

[//]: # Coq (27-30)

A dictator is an individual whose preference is unconditionally adopted by the society.

--MATH_START--
$\mathbf{Definition}$\
An individual $i$ is a dictator if
$$\forall a,b \in A, p \in P, a \succ_i b \Rightarrow a \succ_p b$$
--MATH_END--

[//]: # Coq (32-35)

An individual is said to be a dictator for all alternatives but one if its preference is unconditionally adopted by the society for all these other alternatives.

--MATH_START--
$\mathbf{Definition}$\
An individual $i$ is a dictator except for $b \in A$ if
$$\forall a,c \in A \text{ other than } b, p \in P, a \succ_i c \Rightarrow a \succ_p c$$
--MATH_END--

[//]: # Coq (37-42)

Two alternatives are said to be unanimously in the same order in two preference profiles if they are (strictly) in the same order for every individual.

--MATH_START--
$\mathbf{Definition}$\
Two alternatives $a$ and $b$ are in the same order in preference orders $\succ_1$ and $\succ_2$ if
$$a \succ_1 b \iff a \succ_2 b$$ and $$b \succ_1 a \iff b \succ_2 a$$
In this case, $a$ and $b$ are equivalently indifferent in both orders as well.

$\mathbf{Definition}$\
Two alternatives $a$ and $b$ are unanimously in the same order in preference profiles $p_1$ and $p_2$ if they are in the same order for every individual.
--MATH_END--

[//]: # Coq (44-46)

We say that the independance of irrelevant alternatives is respected if the social preference between two alternatives only depends on the individual preferences between them.

--MATH_START--
$\mathbf{Definition}$\
A constitution $constit$ respects the independance of irrelevant alternatives if $\forall p_1, p_2 \in P, a, b \in A,$
$$a \text{ and } b \text{ are unanimously in the same order in } p_1 \text{ and } p_2 \Rightarrow a \text{ and } b \text{ are in the same order in } constit(p_1) \text{ and } constit(p_2)$$
--MATH_END--

[//]: # Coq (48-51)


## First lemmas, some useful definitions

If there is more than one alternative, an alternative can't be at the same the top choice and the bottom choice in a preference order.

--MATH_START--
$\mathbf{Lemma}$\
If $card(A) \ge 2$ and $b$ is an alternative, $b$ can't be at the same time strictly preferred and strictly unpreferred to all other alternatives.

$\mathbf{proof:}$\
Obvious \
■
--MATH_END--

[//]: # Coq (53-66)

An alternative is said to be an unanimous top (resp. bottom) choice if it's the top (resp. bottom) choice for every individual. It's said to be an unanimous extremal choice if it's one of them.

--MATH_START--
$\mathbf{Definition}$\
An alternative $b$ is an unanimous top choice if
$$\forall i \in I, \forall a \neq b \in A, b \succ_i a$$
An alternative $b$ is an unanimous bottom choice if
$$\forall i \in I, \forall a \neq b \in A, b \prec_i a$$
An alternativeis is an unanimous extremal choice if it's either an unanimous top choice or an unanimous bottom choice.
--MATH_END--

[//]: # Coq (68-77)

In a constitution respecting unanimity, an unanimous top (resp. bottom) choice is the top (resp. bottom) choice for the society.

--MATH_START--
$\mathbf{Lemma}$\
If the constitution respects unanimity and $b \in A$ is an unanimous very top choice then $\forall p \in P, a \neq b \in A, b \succ_p a$. \
If the constitution respects unanimity and $b \in A$ is an unanimous very bottom choice then $\forall p \in P, a \neq b \in A, b \prec_p a$.

$\mathbf{proof:}$\
We prove the lemma in the case of the top choice. The proof in the case of the bottom choice is analogous. \
By definition of a unanimous top choice, $\forall i \in I, \forall a \neq b \in A, b \succ_i a$. \
Let $p \in P$ and $a \neq b \in A$. \
As unanimity is respected, it suffices to show that $p$ unanimously prefers $b$ over $a$. \
Let $i \in I$. We indeed have $b \succ_i a$ because $b$ in an unanimous top choice. \
■
--MATH_END--

[//]: # Coq (79-99)


## Transformations on preference orders

We will be led to: \
- move an alternative at the very top (resp. bottom) of a preference order and of all the individual preferences. \
- move an alternative just above another one in a preference order and of all the individual preferences.

--MATH_START--
$\mathbf{Definition}$\
Let $o \in O$, $p \in P$ and $a, b \in A$. \
We denote: \
- $o_{b \uparrow}$ as the preference order $o$ in which $b$ was moved at the very top \
- $o_{b \downarrow}$ as the preference order $o$ in which $b$ was moved at the very bottom \
- $o_{b \uparrow a}$ as the preference order $o$ in which $b$ was moved just above $a$ \
- $p_{b \uparrow} = (i \in I) \mapsto p(i)_{b \uparrow}$ \
- $p_{b \downarrow} = (i \in I) \mapsto p(i)_{b \downarrow}$ \
- $p_{b \uparrow a} = (i \in I) \mapsto p(i)_{b \uparrow a}$
--MATH_END--

[//]: # Coq (101-417)


# Proof of Arrow's theorem

If there are at least 3 alternatives, an alternative which is not extremal must be strictly above another one and strictly below a third one.

--MATH_START--
$\mathbf{Lemma}$\
If $card(A) \ge 3$ and $b$ is an alternative which is not extremal in a preference order denoted with $\succ$, then $\exists a, c \in A$ such that $a$, $b$ and $c$ are pairwise distinct, $a \succeq b \succeq c$.

$\mathbf{proof:}$\
Not as obvious as it can seem at first sight: the fact that $b$ is not the bottom choice gives us a $a \neq b$ and the fact that $b$ is not the top choice gives us a $c \neq b$ but $a$, $b$ and $c$ are not necessarily pairwise distinct, because we could have $a = c$. \
If so, let $d$ be an alternative different from $a, b, c$. \
If $b \succeq d$, we have $a \succeq b \succeq d$ where $a, b, d$ are pairwise disjoint. \
Else, we have $d \succeq b$, so $d \succeq b \succeq c$ where $b, c, d$ are pairwise disjoint. \
■
--MATH_END--

[//]: # Coq (419-448)

The following lemma is already puzzling: unanimity and the independence of irrelevant alternatives being respected, if an alternative is an extremal choice for every individual, then it must be extremal for the society as well (alhtough one could think that, if half of the citizens adore it and the other half abhor it, the society would rank it somewhere in the middle).

--MATH_START--
$\mathbf{Extremal\text{ }lemma}$\
Let's suppose that $card(A) \ge 3$ and that the constitution respects unanimity  and the independence of irrelevant alternatives. \
If an alternative is an unanimous extremal choice, then it's an extremal choice for the society as well.

$\mathbf{proof:}$\
Let $b$ be an unanimous extremal choice. \
Let's reason by contradiction and suppose that $b$ is not an extremal choice. \
Then, according to the previous lemma, there $a, c \in A$ such that $a, b, c$ are pairwise distinct and $a \succeq b \succeq c$. \
Let's consider making $c$ above $a$ for every individual. For individuals for which $b$ is the top choice, we keep $b \succ_i c$ and $b \succ_i a$. For the ones for which $b$ is the bottom choice, we keep $c \succ_i b$ and $a \succ_i b$. By independence of irrelevant alternatives, we keep $a \succeq b$ and $b \succeq c$, and therefore $a \succeq c$ by transitivity. \
But, making $c$ above $a$ for every individual makes $c \succ a$ for the whole society by unanimity, which gives a contradiction. \
■
--MATH_END--

[//]: # Coq (450-689)

--MATH_START--
$\mathbf{Definition}$\
Let $constit$ a constitution, $b \in A$ and $i \in I$. \
$i$ is pivotal for $b$ if there are $p, p' \in P$ such that: \
- $\forall j \neq i \in I, p(j) = p'(j)$ \
- $\forall j \in I$, $b$ is an extremal choice in $p(j)$ and $p'(j)$ \
- $b$ is the bottom choice for $p(i)$ \
- $b$ is the top choice for $p'(i)$ \
- $b$ is the bottom choice for $constit(p)$ \
- $b$ is the top choice for $constit(p')$ \
$b$ has a pivot if $\exists i \in I$ such that $i$ is pivotal for $b$.
--MATH_END--

[//]: # Coq (691-703)

--MATH_START--
$\mathbf{Lemma\text{ }1}$\
Let's suppose that $card(A) \ge 3$ and that the constitution respects unanimity  and the independence of irrelevant alternatives. \
Let $b \in A$. If: \
- $\forall i \in I$, $b$ is an extremal choice for $i$ \
- $\exists i \in I$ for which $b$ is the bottom choice \
- $b$ is bottom choice for the society \
Then $b$ has a pivot.

$\mathbf{proof:}$\
We proceed by induction on the number of individuals for which $b$ is the bottom choice. \
If there is no such individual, one of our hypotheses is false, which makes the statement true ($⊥$ implies everything). \
Now we suppose the statement is true if the number of individuals for which $b$ is the bottom choice is $n$ and want to prove it if the number of individuals for which $b$ is the bottom choice is $n+1$. \
Let $i$ for which $b$ is the bottom choice. \
Let's make $b$ the top choice for $i$. According to the extremal lemma, doing so will either make $b$ the top choice for the society either let it unchangedly the bottom choice for the society. \
$\underline{\text{First case}}$: $b$ remains the bottom choice for the society \
We can apply the induction hypothesis on the profile obtained by making $b$ the top choice for $i$, which gives us immediately that $i$ is pivotal (this fact doesn't depend on individual preferences). \
$\underline{\text{Second case}}$: $b$ becomes the top choice for the society \
Here $i$ is pivotal just by definition (considering $p'$ as the profile by making $b$ the top choice for $i$). \
■
--MATH_END--

[//]: # Coq (705-1050)

--MATH_START--
$\mathbf{Lemma\text{ }2}$\
Let's suppose that $card(A) \ge 3$ and that the constitution respects unanimity and the independence of irrelevant alternatives. \
Then every $b \in A$ has a pivot.

$\mathbf{proof:}$\
Let $b \in A$. \
Let $p$ be the preference profile obtained by making $b$ the bottom chioce and all the other alternatives indiiferent for every individual. \
There, $b$ is the bottom choice for the society by unanimity, and we can conclude by a straightforward application of lemma 1. \
■
--MATH_END--

[//]: # Coq (1052-1091)

--MATH_START--
$\mathbf{Lemma\text{ }3}$\
Let's suppose that the constitution respects the independence of irrelevant alternatives and that $i \in I$ is pivotal for $b \in A$. \
Then $i$ is a dictator except for $b$.

$\mathbf{proof:}$\
Let $a \neq b, c \neq b \in A$ and $p \in P$. \
Let's suppose $c \succ_{i} a$. We have to prove $c \succ_p a$. \
Let $p_1$ and $p_2$ preference profiles given by the fact that $i$ is pivotal for $b$. We thus have: \
- $\forall j \neq i \in I, p_1(j) = p_2(j)$ \
- $\forall j \in I$, $b$ is an extremal choice in $p_1(j)$ and $p_2(j)$ \
- $b$ is the bottom choice for $p_1(i)$ \
- $b$ is the top choice for $p_2(i)$ \
- $b$ is the bottom choice for $constit(p_1)$ \
- $b$ is the top choice for $constit(p_2)$ \
Let $p'$ defined by:
$$ j \in I \mapsto \begin{cases*}
  p(i)_{b \uparrow a} \text{ if } j = i \\
  p(j)_{b \downarrow} \text{ if } j \neq i \text{ and } b \text{ is the bottom choice for } j \text{ in } p_1 \\
  p(j)_{b \uparrow} \text{ if } j \neq i \text{ and } b \text{ is not the bottom choice for } j \text{ in } p_1 \\
\end{cases*} $$
In either case, $a$ and $c$ remain (strictly) in the same order in $p(j)$ and $p'(j)$ whatever $j \in I$, and therefore (strictly) in the same order in $constit(p)$ and $constit(p')$ by independence of the irrelevant alternatives. So it suffices to show that $c \succ_{p'} a$. \
By transitivity, it suffices to show that $c \succ_{p'} b$ and $b \succ_{p'} a$. \
To prove $c \succ_{p'} b$ it suffices to show that $b$ and $c$ are in the same order for every individual in $p_1$ and $p'$ (and conclude with the independence of irrelevant alternatives, as $c \succ_{p_1} b$ stands because $b$ is the bottom choice for $constit(p_1)$). \
For individual $i$, our hypothesis $c \succ_{i} a$ in $p$ is unchanged when applying the $b \uparrow a$ operator, so $c \succ_{i} a$ in $p'$, which gives $c \succ_{i} b$ in $p'$ by definition of the $b \uparrow a$ operator (wa have $c \neq b$ by hypothesis). And $c \succ_{i} a$ in $p_1$ because $b$ is the bottom choice for $p_1(i)$. \
For individuals $j \neq i$ such that $b$ is the bottom choice in $p_1$, $b$ is also the bottom choice in $p'$ by definition of $p'$, so that $b$ and $c$ are in the same order in $p_1$ and $p'$. \
For individuals $j \neq i$ such that $b$ is not the bottom choice in $p_1$, $b$ is the top choice in $p'$ by definition of $p'$ and $b$ is the top choice in $p_1$ (it is extremal by definition of $p_1$), so that $b$ and $c$ are in the same order in $p_1$ and $p'$. \
To prove $b \succ_{p'} a$ it suffices to show that $a$ and $b$ are in the same order for every individual in $p_2$ and $p'$ (and conclude with the independence of irrelevant alternatives, as $b \succ_{p_2} a$ stands because $b$ is the top choice for $constit(p_2)$). \
For individual $i$, $b \succ_{i} a$ in $p'$ by definition of the $b \uparrow a$ operator and $b \succ_{i} a$ in $p_2$ because $b$ is the top choice in $p_2$. \
For individuals $j \neq i$ such that $b$ is the bottom choice in $p_1$, $b$ is also the bottom choice in $p'$ by definition of $p'$ and it's the bottom choice in $p_2$ (because $p_2(j)=p_1(j)$), so that $b$ and $c$ are in the same order in $p_2$ and $p'$. \
For individuals $j \neq i$ such that $b$ is not the bottom choice in $p_1$, $b$ is the top choice in $p'$ by definition of $p'$ and $b$ is the top choice in $p_1$ (it is extremal by definition of $p_1$) and therefore the top choice in $p_2$ (because $p_2(j)=p_1(j)$), so that $b$ and $c$ are in the same order in $p_2$ and $p'$. \
■
--MATH_END--

[//]: # Coq (1093-1523)

--MATH_START--
$\mathbf{Lemma\text{ }4}$\
Let's suppose that: \
- $card(A) \ge 3$ \
- the constitution respects the independence of irrelevant alternatives \
- every alternative has a pivot \
Then there is a dictator.

$\mathbf{proof:}$\
Let $b \in A$. Let $i$ be a pivot of $b$. \
By lemma 3, $i$ is a dictator except for $b$. \
Let $b' \neq b \in A$. Let $i'$ be a pivot of $b'$. \
By lemma 3, $i'$ is a dictator except for $b'$. \
It remains to show that $i = i'$ (then $i$ will be a dictator for $b$ as well). \
Let $a \in A$ other than $b$ and $b'$. Then $i$ and $i'$ are both dictators for $a$, but there can be only one dictator (because the society can't adopt the votes of two dictators when they differ), so that $i=i'$.
■
--MATH_END--

[//]: # Coq (1525-1640)

--MATH_START--
$\mathbf{Arrow's\text{ }theorem}$\
Let's suppose that $card(A) \ge 3$ and that the constitution respects unanimity and the independence of irrelevant alternatives. \
Then one of the individuals is a dictator.

$\mathbf{proof:}$\
Every alternative has a pivot by lemma 2. Then lemma 4 immediately gives a dictator. \
■
--MATH_END--

[//]: # Coq (1642-1652)
