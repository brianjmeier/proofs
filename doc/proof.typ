#set page(paper: "a4", margin: 2.5cm)
#set text(font: "New Computer Modern", size: 11pt)
#set heading(numbering: "1.1.")
#set par(justify: true)

#align(center, text(17pt, weight: "bold")[
  Subgrupos Cíclicos y la Reducción por Mitades
])

#align(center, text(12pt)[
  Una construcción algebraica paso a paso
])

= Construyendo $F$ y $D$

Empecemos con un campo finito $F$. Dentro de sus elementos no nulos $F^times$, elegimos un elemento $omega$ que sea una raíz primitiva de orden $2^n$. Esto significa simplemente:

$ omega^(2^n) = 1, $
y ninguna potencia positiva menor de $omega$ da $1$.

A partir de $omega$, construimos una cadena de subconjuntos $D_0, D_1, D_2, dots$ donde cada uno es el conjunto de potencias de un generador:

$ D_k := angle.l omega^(2^k) angle.r = {1, omega^(2^k), omega^(2 dot 2^k), omega^(3 dot 2^k), dots}. $

En palabras sencillas: $D_k$ es el grupo cíclico generado por $omega^(2^k)$.

= ¿Qué es un grupo cíclico?

Un *grupo cíclico* es uno que puede generarse con un solo elemento. Si tomamos un elemento $g$ y miramos todas sus potencias ${1, g, g^2, g^3, dots}$, eventualmente volvemos a $1$ (porque estamos en un grupo finito). El número de elementos distintos antes de repetirse se llama el *orden* del grupo.

Para $D_k$, el generador es $omega^(2^k)$, y queremos saber: ¿cuántos elementos tiene?

= Un ejemplo concreto

Antes de probar nada, veamos qué pasa con $n = 3$, es decir, $omega$ tiene orden $2^3 = 8$.

*Paso 0:* $D_0 = angle.l omega angle.r = {1, omega, omega^2, omega^3, omega^4, omega^5, omega^6, omega^7}$.
Tiene $8$ elementos.

*Paso 1:* $D_1 = angle.l omega^2 angle.r = {1, omega^2, omega^4, omega^6}$.
Las potencias de $omega^2$ dan solo $4$ elementos distintos porque $(omega^2)^4 = omega^8 = 1$.
Tiene $4$ elementos.

*Paso 2:* $D_2 = angle.l omega^4 angle.r = {1, omega^4}$.
Tiene $2$ elementos.

*Paso 3:* $D_3 = angle.l omega^8 angle.r = {1}$.
Tiene $1$ elemento.

Observamos un patrón claro: $8 -> 4 -> 2 -> 1$. Cada paso divide por $2$.

= La hipótesis

Del ejemplo anterior, surge una hipótesis natural:

*Hipótesis.* Para cada $k < n$, el orden de $D_k$ es exactamente el doble que el orden de $D_(k+1)$:

$ |D_k| = 2 dot |D_(k+1)|. $

Equivalentemente: $|D_(k+1)| = |D_k| / 2$.

¿Es esto siempre cierto, o fue una casualidad del ejemplo? Veamos.

= La prueba por inducción

Vamos a probar que $|D_k| = 2^(n-k)$ para todo $k <= n$. Esto implica automáticamente que se reduce a la mitad en cada paso.

*Teorema.* Para todo $k <= n$, se cumple $|D_k| = 2^(n-k)$.

*Prueba por inducción sobre $k$.*

*Caso base* ($k = 0$): $D_0 = angle.l omega angle.r$. Como $omega$ tiene orden $2^n$ por definición:

$ |D_0| = 2^n = 2^(n-0). #h(1em) checkmark $

*Paso inductivo:* Supongamos que $|D_k| = 2^(n-k)$ para algún $k < n$. Queremos probar que $|D_(k+1)| = 2^(n-(k+1))$.

La clave está en observar que $D_(k+1)$ consiste exactamente en los cuadrados de los elementos de $D_k$. Es decir:

$ D_(k+1) = {x^2 : x in D_k}. $

El mapeo $x |-> x^2$ envía $D_k$ sobre $D_(k+1)$. En un grupo cíclico de orden par, la ecuación $x^2 = 1$ tiene exactamente dos soluciones: $x = 1$ y $x = -1$. Por lo tanto, cada elemento de $D_(k+1)$ proviene de exactamente $2$ elementos de $D_k$.

Concluimos que:

$ |D_(k+1)| = |D_k| / 2 = 2^(n-k) / 2 = 2^(n-k-1) = 2^(n-(k+1)). #h(1em) checkmark $

Esto completa la inducción.

= Resumen

#table(
  columns: (1fr, 1fr),
  inset: 8pt,
  align: center,
  table.header([Paso], [Resultado]),
  [Definición de $D_k$], [$D_k = angle.l omega^(2^k) angle.r$],
  [Caso base], [$|D_0| = 2^n$],
  [Hipótesis observada], [$|D_k| = 2 dot |D_(k+1)|$],
  [Teorema inductivo], [$|D_k| = 2^(n-k)$ para todo $k <= n$],
  [Consecuencia], [La cadena $D_0, D_1, dots, D_n$ reduce el orden a la mitad en cada paso],
)

Empezamos con $|D_0| = 2^n$ y terminamos con $|D_n| = 1$. En $n$ pasos, el grupo se colapsa a un solo elemento. Esta reducción exponencial es la propiedad algebraica fundamental que hace posible construir protocolos eficientes sobre esta estructura.
