#set page(paper: "a4", margin: 2.5cm)
#set text(font: "New Computer Modern", size: 11pt)
#set heading(numbering: "1.1.")
#set par(justify: true)

#align(center, text(17pt, weight: "bold")[
  Low Degree Proof — Protocolo FRI
])

#align(center, text(12pt)[
  Demostración de que $|D_(k+1)| = |D_k|/2$ por inducción
])

#align(center, text(10pt, style: "italic")[
  Campo finito, subgrupos cíclicos, y homomorfismos de reducción
])

= Contexto

El protocolo _FRI_ (_Fast Reed-Solomon IOP of Proximity_) es un componente central en las pruebas de conocimiento cero transparentes (zk-STARKs). En cada ronda del FRI, el _dominio de evaluación_ se reduce a la mitad. Esto es posible porque el dominio es un subgrupo cíclico de orden potencia de 2, y elevar al cuadrado es un homomorfismo sobreyectivo cuyo kernel tiene exactamente 2 elementos.

En este documento formalizamos esta observación.

= Definiciones

Sea $F$ un campo finito y $omega in F^times$ una raíz primitiva $2^n$-ésima de la unidad. Definimos los dominios de evaluación como los subgrupos cíclicos generados por las potencias sucesivas de $omega$:

$ D_k := angle.l omega^(2^k) angle.r subset.eq F^times. $

En Lean 4, esto se modela como:

```lean
def friDomain (k : ℕ) : Subgroup Fˣ := Subgroup.zpowers (ω ^ (2 ^ k))
```

Notar que $D_0 = angle.l omega angle.r$ tiene orden $2^n$, $D_1 = angle.l omega^2 angle.r$ tiene orden $2^(n-1)$, y en general $D_k$ tiene orden $2^(n-k)$.

= Resultado principal

== Teorema (Cardinalidad de $D_k$)

Para todo $k <= n$,

$ |D_k| = 2^(n-k). $

*Demostración (en Lean 4):*

Primero probamos que el orden del generador es correcto. Usamos la fórmula estándar
$ "ord"(g^m) = "ord"(g) / gcd("ord"(g), m) $
junto con el hecho de que $gcd(2^n, 2^k) = 2^k$ cuando $k <= n$:

```lean
theorem order_omega_pow (k : ℕ) (hk : k ≤ n) :
    orderOf (ω ^ (2 ^ k)) = 2 ^ (n - k) := by
  rw [orderOf_pow, hω]
  have h_gcd : Nat.gcd (2 ^ n) (2 ^ k) = 2 ^ k := by
    have h_dvd : 2 ^ k ∣ 2 ^ n := by exact Nat.pow_dvd_pow 2 (by omega)
    rw [Nat.gcd_comm]
    exact Nat.gcd_eq_left h_dvd
  rw [h_gcd]
  exact Nat.pow_div (by omega) (by norm_num)
```

Luego, como $D_k$ es cíclico generado por $omega^(2^k)$, su cardinalidad es exactamente el orden del generador. En un grupo finito, el subgrupo cíclico $angle.l g angle.r$ tiene $|angle.l g angle.r| = "ord"(g)$ elementos.

== Corolario (Reducción a la mitad)

Para todo $k < n$,

$ |D_k| = 2 dot |D_(k+1)| quad "y equivalentemente" quad |D_(k+1)| = |D_k|/2. $

*Demostración (en Lean 4):*

```lean
theorem friDomain_halving (k : ℕ) (hk : k < n) :
    Nat.card (friDomain ω k) = 2 * Nat.card (friDomain ω (k + 1)) := by
  have h1 := friDomain_card ω n hω k (by omega)
  have h2 := friDomain_card ω n hω (k + 1) (by omega)
  rw [h1, h2]
  have h_exp : n - k = (n - (k + 1)) + 1 := by omega
  rw [h_exp]
  ring
```

La reducción a $|D_(k+1)| = |D_k|/2$ se deduce inmediatamente porque $|D_(k+1)| > 0$ (es una potencia de 2).

= Demostración por inducción

El teorema $|D_k| = 2^(n-k)$ también se puede probar directamente por inducción sobre $k$, lo cual refleja exactamente la estructura del protocolo FRI:

*Caso base* $(k = 0)$: $D_0 = angle.l omega angle.r$, y $|D_0| = "ord"(omega) = 2^n$. $checkmark$

*Paso inductivo*: si $|D_k| = 2^(n-k)$, entonces por el corolario de reducción a la mitad:

$ |D_(k+1)| = |D_k|/2 = 2^(n-k)/2 = 2^(n-(k+1)). checkmark $

En Lean 4:

```lean
theorem friDomain_card_by_induction (k : ℕ) (hk : k ≤ n) :
    Nat.card (friDomain ω k) = 2 ^ (n - k) := by
  induction k with
  | zero =>
    exact friDomain_card ω n hω 0 (by omega)
  | succ k ih =>
    have h_k_le_n : k ≤ n := by omega
    have h_k_lt_n : k < n := by omega
    have h_Dk : Nat.card (friDomain ω k) = 2 ^ (n - k) := ih h_k_le_n
    have h_Dk1 : Nat.card (friDomain ω (k + 1)) = Nat.card (friDomain ω k) / 2 :=
      friDomain_next_card ω n hω k h_k_lt_n
    rw [h_Dk1, h_Dk]
    have h_exp : n - k = (n - (k + 1)) + 1 := by omega
    rw [h_exp]
    -- 2^(m+1) / 2 = 2^m
    have : 2 ^ (n - (k + 1) + 1) / 2 = 2 ^ (n - (k + 1)) := by
      rw [show 2 ^ (n - (k + 1) + 1) = 2 ^ (n - (k + 1)) * 2 by ring]
      simp
    rw [this]
```

= Perspectiva vía homomorfismos (primer teorema del isomorfismo)

La reducción a la mitad tiene una explicación estructural elegante. Consideremos el homomorfismo

$ phi : D_k arrow.r F^times, quad phi(x) = x^2. $

- $phi$ es sobreyectivo sobre $D_(k+1)$, porque todo elemento de $D_(k+1) = angle.l omega^(2^(k+1)) angle.r$ es un cuadrado en $D_k$.
- El kernel es $ker(phi) = {x in D_k : x^2 = 1}$. Como $D_k$ es cíclico de orden $2^(n-k) >= 2$ (pues $k < n$), la ecuación $x^2 = 1$ tiene exactamente 2 soluciones: $x = 1$ y $x = -1 = g^(2^(n-k-1))$.

Por el primer teorema del isomorfismo:

$ D_k / ker(phi) tilde.equiv im(phi) = D_(k+1) $

y por tanto

$ |D_(k+1)| = |D_k| / |ker(phi)| = |D_k| / 2. $

En Lean 4, el esqueleto de esta prueba es:

```lean
theorem friDomain_kernel_size (k : ℕ) (hk : k < n) [NeZero (2 : F)] :
    let φ : (friDomain ω k) →* Fˣ :=
      MonoidHom.mk' (fun (x : (friDomain ω k)) => (x.val ^ 2)) (by intros; simp [mul_pow])
    Nat.card (MonoidHom.ker φ) = 2 := by
  sorry  -- requiere estructura adicional de grupos cíclicos
```

= Resumen

#table(
  columns: (1fr, 1fr, 1fr),
  inset: 8pt,
  align: center,
  table.header([Paso], [Matemática], [Lean 4]),
  [Definición], [$D_k = angle.l omega^(2^k) angle.r$], [`friDomain k`],
  [Orden del generador], [$"ord"(omega^(2^k)) = 2^(n-k)$], [`order_omega_pow`],
  [Cardinalidad], [$|D_k| = 2^(n-k)$], [`friDomain_card`],
  [Reducción], [$|D_(k+1)| = |D_k|/2$], [`friDomain_next_card`],
  [Inducción], [$|D_k| = 2^(n-k)$ para todo $k <= n$], [`friDomain_card_by_induction`],
  [Kernel], [$|ker(phi)| = 2$], [`friDomain_kernel_size` (esqueleto)],
)

Este resultado justifica la reducción logarítmica del dominio en cada ronda del protocolo FRI, que es la clave de su eficiencia.
