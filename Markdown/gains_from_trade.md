---
title: "The gains from trade"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - Economics
...


## Presentation

This page gives the formalization of the [the gains from trade](https://socialsci.libretexts.org/Bookshelves/Economics/Introductory_Comprehensive_Economics/Principles_of_Economics_(LibreTexts)/17%3A_International_Table/17.1%3A_The_Gains_from_Trade), which state roughly that if one of two enitities (persons, individuals, corporations or countries) is more efficient at producing a good $G_1$ but less efficient at producing a good $G_2$ than the other one, then both entities end up with more goods if they specialize in the good in which they are efficient and then trade with one another (than if they are self-suffcient).

--MATH_START--
Throughout this page, let $C$ the set of commodities (that is goods or services) and $E$ the finite set of entities.
Quantities of commodities are measured with nonnegative real numbers (whose set is denoted ${\mathbb R}_+)$. One could have used natural numbers, but real ones are more convenient as we will be led to divide by 2.
--MATH_END--

[//]: # Rocq (28-33)


## Notion of capacity

One can produce a finite (possibly null) quantity of every good or service and one can decrease one's production at will.

--MATH_START--
$\mathbf{Definition}$\
Let $WP = {\mathbb R}_+ ^ C$ be the set of work products, a work product giving a produced quantity for each commodity. \
Unprodictivity means producing none of any commodity.
--MATH_END--

[//]: # Rocq (35-38)

--MATH_START--
$\mathbf{Definition}$\
A work product $wp \in WP$ is said at least as productive as another one $wp' \in WP$ if
$$\forall c\in C, wp'c \le wp$$
--MATH_END--

[//]: # Rocq (40-42)

--MATH_START--
$\mathbf{Definition}$\
Let $c \in C$ a commodity and $q \in {\mathbb R}_+$ a quantity (of the commodity $c$). \
A function $d : WP \rightarrow \{⊥ ,⊤\}$ telling when a production is doable (possible) or not, the quantity $q$ is said producible for $c$ if $\exists wp \in WP, d(wp) = ⊤$ and $wp(c)=q$.
--MATH_END--

[//]: # Rocq (44-46)

--MATH_START--
$\mathbf{Definition}$\
Let $d : WP \rightarrow \{⊥ ,⊤\}$ a function telling when a production is doable or not. \
The production is said finite if $\forall c \in C, \exists M \in {\mathbb R}_+$ such that $\forall q \in {\mathbb R}_+$, if $q$ is producible for $c$ then $q \le M$.
--MATH_END--

[//]: # Rocq (48-49)

--MATH_START--
$\mathbf{Definition}$\
Let $d : WP \rightarrow \{⊥ ,⊤\}$ a function telling when a production is doable or not. \
The production is said decreasable at will if $\forall wp wp' \in WP$, if $wp$ is at least as productive as $wp'$ and $d(wp) = ⊤$ then $d(wp') = ⊤$.
--MATH_END--

[//]: # Rocq (51-55)

--MATH_START--
$\mathbf{Definition}$\
Let $d : WP \rightarrow \{⊥ ,⊤\}$ a function. \
$d$ is said to define a capacity if: \
- unproductivity is satisfied by $d$ \
- the production is finite \
- the production is decreasable at will
--MATH_END--

[//]: # Rocq (57-119)

--MATH_START--
$\mathbf{Definition}$\
The total production is the sum of work products by each entity.
--MATH_END--

[//]: # Rocq (124-161)


## Efficiency

A production is efficient if increasing the production of a commodity necessarily implies decreasing the production of (at least) one other coomodity.

--MATH_START--
$\mathbf{Definition}$\
Let $d : WP \rightarrow \{⊥ ,⊤\}$ a function defining a capacity. \
A work product $wp \in WP$ is said efficient if: \
- $wp$ is doable according to $d$ \
- $\forall wp'$ doable according to $d$, if $\exists c \in C$ such that $wp(c) < wp'(c)$, then $\exists c \in C$ such that $wp'(c) < wp(c)$.
--MATH_END--

[//]: # Rocq (163-203)

--MATH_START--
$\mathbf{Definition}$\
Let $d : WP \rightarrow \{⊥ ,⊤\}$ a function defining a capacity. \
Let $c \in C$ a commodity. Let quantities for each other commodity given in $oq \in WP$. \
If there exists a quantity $q \in {\mathbb R}_+$ such that $oq_{c \leftarrow q}$ is doable according to $d$, one says that the precision is finite if $oq_{c \leftarrow { sup \{q \in {\mathbb R}_+ / oq_{c \leftarrow q} \text{ is doable } \} }}$ is also doable according to $d$, that is if the least upper bound of $\{q \in {\mathbb R}_+ / oq_{c \leftarrow q} \text{ is doable } \}$ is a maximum.
--MATH_END--

[//]: # Rocq (205-209)


## Trade

The simplest form of trade is a barter of a certain quantity of a good or service for a certain quantity of another good or service between two entities.

--MATH_START--
$\mathbf{Definition}$\
Let $r \in WP^E$ a repartition, that is the data of what quantity of each commoodity every entity has. \
Let $i, j \in E$ be entities, $c_1, c_2 \in C$ be commodities and $q_1, q_2 \in {\mathbb R}_+$ quantities such that $q_1 \le r(i, c_1)$ and $q_2 \le r(j, c_2)$. \
A barter is the operation which leads to a new repartition, in which $is's quantity of $c_1$ is diminished by $q_1$ whereas the quantity of $c_2$ is increased by $q_2$ (and reversely for $j$).
--MATH_END--

[//]: # Rocq (211-246)

By dint of barters and possibly transactions involving more than two entities, goods and services have changed hands, but the total quantity of each (non-consumed) good remains unchanged.

--MATH_START--
$\mathbf{Definition}$\
A function $at \in WP^E \rightarrow WP^E$ assigning a repartition to another one is said to preserve the total production if
$$\forall r \in WP^E, \forall c \in C, \sum_{e \in E} r(e, c) = \sum_{e \in E} at(r)(e, c)$$
--MATH_END--

[//]: # Rocq (248-383)


## Opportunity cost and comparative advantage

In an efficient production the opportunity cost of increasing the production of a good to a certain quantity is how much one must decrease the production of another good to make this increase (the other goods' productions remaining unchanged, keeping efficiency).

--MATH_START--
$\mathbf{Definition}$\
Let $c_1, c_2 \in C$ be distinct commodities. \
Let quantities for each other commodity given in $oq \in WP$. \
Let $d : WP \rightarrow \{⊥ ,⊤\}$ a function defining a capacity. \
Let $q_1, q_1', q_2 \in {\mathbb R}_+$ quantities such that $q_1 \lt q_1'$. \
Let's suppose that $oq_{c_1 \leftarrow q_1, c_2 \leftarrow q_2}$ is effcient and that $\exists q_2' \in {\mathbb R}_+$ such that $oq_{c_1 \leftarrow q_1', c_2 \leftarrow q_2'}$ is doable. \
Then the opportunity cost of increasing $c_1$ to $q_1'$ relatively to $c_2$ is defined as $q_2 - sup \{q \in {\mathbb R}_+ / oq_{c_1 \leftarrow q_1', c_2 \leftarrow q} \text{ is doable }\}$.
--MATH_END--

[//]: # Rocq (385-463)

An entity has a comparative advantage over another entity if its opportunity cost is lower.

--MATH_START--
$\mathbf{Definition}$\
Let $i, j \in E$ be different entities and $c_1, c_2 \in C$ be distinct commodities. \
Let quantities for each other commodity given in $oq \in WP$. \
Let $d : WP \rightarrow \{⊥ ,⊤\}$ a function defining a capacity. \
Let $q_{1i}, q'_{1i}, q_{2i}, q_{1j}, q'_{1j}, q_{2j} \in {\mathbb R}_+$ quantities such that $q_{1i} \lt q'_{1i}$ and $q_{1j} \lt q'_{1j}$. \
Let's suppose that: \
- $oq_{c_1 \leftarrow q_{1i}, c_2 \leftarrow q_{2i}}$ is effcient \
- $oq_{c_1 \leftarrow q_{1j}, c_2 \leftarrow q_{2j}}$ is effcient \
- $\exists q_{2i}' \in {\mathbb R}_+$ such that $oq_{c_1 \leftarrow q'_{1i}, c_2 \leftarrow q_{2i}'}$ is doable. \
- $\exists q_{2j}' \in {\mathbb R}_+$ such that $oq_{c_1 \leftarrow q'_{1j}, c_2 \leftarrow q_{2j}'}$ is doable. \
Then $i$ has a comparative advantage over $j$ on $c_1$ relatively to $c_2$ if its opportunity cost is less than $j$'s one.
--MATH_END--

[//]: # Rocq (465-479)


## Ricardo's argument

If an entity has a comparative advantage over another entity, they can with trade reach a level of wealth they could not have without, in the sense that they own greater quantities of goods than if they had stayed in autarky.

--MATH_START--
$\mathbf{Ricardo's\text{ }theorem}$\
Let $i, j \in E$ be different entities and $c_1, c_2 \in C$ be distinct commodities. \
Let quantities for each other commodity given in $oq \in WP$. \
Let $d : WP \rightarrow \{⊥ ,⊤\}$ a function defining a capacity. \
Let $q_{1i}, q_{2i}, q_{1j}, q_{2j}, δ \in {\mathbb R}_+$ quantities such that $0 < δ$. \
Let's suppose that: \
- $oq_{c_1 \leftarrow q_{1i}, c_2 \leftarrow q_{2i}}$ is effcient \
- $oq_{c_1 \leftarrow q_{1j}, c_2 \leftarrow q_{2j}}$ is effcient \
- $\exists q_{2i}' \in {\mathbb R}_+$ such that $oq_{c_1 \leftarrow q'_{1i}, c_2 \leftarrow q_{2i}'}$ is doable \
- $\exists q_{2j}' \in {\mathbb R}_+$ such that $oq_{c_1 \leftarrow q'_{1j}, c_2 \leftarrow q_{2j}'}$ is doable \
- $i$ has a comparative advantage over $j$ on $c_1$ relatively to $c_2$ (let $oc_i$ and $oc_j$ be the opportunity costs of $i$ and $j$ respectively) \
- there is a finite precision of $oq_{c_1 \leftarrow q_{1i} + δ}$ on $c_2$ \
Then, in a situation where: \
- $i$ is effcient and produces $q_{1i} + δ$ of $c_1$ \
- $j$ is effcient and produces $q_{1j}$ of $c_1$ \
both entities reach a repartition they could not have without trade if $i$ gives to $j$ $δ$ of $c_1$ in exchange for $\frac {oc_i + oc_j} 2$ of $c_2$.

$\mathbf{proof:}$\
By efficiency and precision, before the barter: \
- $i$ has $q_{1i} + δ$ of $c_1$ and $max \{q \in {\mathbb R}_+ / oq_{c_1 \leftarrow q_{1i} + δ, c_2 \leftarrow q} \text{ is doable }\}$ of $c_2$ (let's call $q_{2i}'$ this maximum) \
- $j$ has $q_{1j}$ of $c_1$ and $q_{2j}$ of $c_2$ \
And after the barter: \
- $i$ has $q_{1i}$ of $c_1$ and $q_{2i}' + \frac {oc_i + oc_j} 2$ of $c_2$ \
- $j$ has $q_{1j} + δ$ of $c_1$ and $q_{2j} - \frac {oc_i + oc_j} 2$ of $c_2$ \
Let $q_{2j}' = sup \{q \in {\mathbb R}_+ / oq_{c_1 \leftarrow q_{1j} + δ, c_2 \leftarrow q} \text{ is doable }\}$ \
By definition of opportunity cost, $oc_i = q_{2i} - q_{2i}'$ and $oc_j = q_{2j} - q_{2j}'$. \
By our hypothesis of comparative advantage we have $oc_i < oc_j$. \
Which gives $q_{2i} - q_{2i}' < q_{2j} - q_{2j}'$. \
On the one hand, \
$q_{2i} - q_{2i}' < q_{2j} - q_{2j}'$ \
$\Leftrightarrow 2 q_{2i} - q_{2i}' < q_{2i} + q_{2j} - q_{2j}'$ \
$\Leftrightarrow 2 q_{2i} < 2 q_{2i}' + q_{2i} - q_{2i}' + q_{2j} - q_{2j}'$ \
$\Leftrightarrow q_{2i} < q_{2i}' + \frac {(q_{2i} - q_{2i}') + (q_{2j} - q_{2j}')} 2$ \
$\Leftrightarrow q_{2i} < q_{2i}' + \frac {oc_i + oc_j} 2$ \
As by efficiency of $oq_{c_1 \leftarrow q_{1i}, c_2 \leftarrow q_{2i}}$, $max \{q \in {\mathbb R}_+ / oq_{c_1 \leftarrow q_{1i}, c_2 \leftarrow q} \text{ is doable }\} = q_{2i}$, we have $max \{q \in {\mathbb R}_+ / oq_{c_1 \leftarrow q_{1i}, c_2 \leftarrow q} \text{ is doable }\}$ less than the quantity of $c_2$ which $i$ has after the barter. \
So that the repartition after the barter is not doable for $i$, that is out of capacity. \
On the other hand, \
$q_{2i} - q_{2i}' < q_{2j} - q_{2j}'$ \
$\Leftrightarrow 2 q_{2j}' < 2 q_{2j} - (q_{2i} - q_{2i}' + q_{2j} - q_{2j}')$ \
$\Leftrightarrow q_{2j}' < q_{2j} - \frac {(q_{2i} - q_{2i}') + (q_{2j} - q_{2j}')} 2$ \
$\Leftrightarrow q_{2j}' < q_{2j} - \frac {oc_i + oc_j} 2$ \
By definition of $q_{2j}'$, we have $sup \{q \in {\mathbb R}_+ / oq_{c_1 \leftarrow q_{1j} + δ, c_2 \leftarrow q} \text{ is doable }\}$ less than the quantity of $c_2$ which $j$ has after the barter. \
So that the repartition after the barter is not doable for $j$, that is out of capacity. \
■
--MATH_END--

[//]: # Rocq (481-1157)
