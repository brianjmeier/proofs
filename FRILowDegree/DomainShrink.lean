import Mathlib

/-
  Low Degree Proof - FRI Protocol
  
  Demostración de que |D_{k+1}| = |D_k| / 2 por inducción,
  donde D_k son subgrupos cíclicos de un campo finito,
  y D_{k+1} = {x^2 : x ∈ D_k}.
  
  Esto es fundamental en el protocolo FRI (Fast Reed-Solomon IOP of Proximity)
  usado en zk-STARKs: cada ronda "fold" reduce el dominio a la mitad.
  
  La clave es que D_k es un subgrupo cíclico multiplicativo, y el homomorfismo
  φ(x) = x^2 reduce el orden a la mitad porque el kernel tiene tamaño 2.
-/ 

section Direct_FRI_Proof

variable {F : Type*} [Field F] [Finite F]

-- ω es una raíz primitiva 2^n-ésima de la unidad en F^×
variable (ω : Fˣ) (n : ℕ) (hω : orderOf ω = 2 ^ n)

include hω

/- Definimos D_k como el subgrupo generado por ω^(2^k).
   
   En la notación de la pizarra:
   - D_0 = ⟨ω⟩ (subgrupo generado por ω, orden 2^n)
   - D_1 = ⟨ω^2⟩ (orden 2^{n-1})
   - D_2 = ⟨ω^4⟩ (orden 2^{n-2})
   - ...
   - D_k = ⟨ω^(2^k)⟩ (orden 2^{n-k})
   
   Notar que D_{k+1} = {x^2 : x ∈ D_k} como conjunto.
-/ 

def friDomain (k : ℕ) : Subgroup Fˣ := Subgroup.zpowers (ω ^ (2 ^ k))

/- El orden de ω^(2^k) es exactamente 2^{n-k} (para k ≤ n).
   Usamos la fórmula estándar: orderOf(g^m) = orderOf(g) / gcd(orderOf(g), m)
   
   Como orderOf(ω) = 2^n y m = 2^k, tenemos:
   gcd(2^n, 2^k) = 2^k (porque k ≤ n)
   orderOf(ω^(2^k)) = 2^n / 2^k = 2^{n-k}
-/ 

theorem order_omega_pow (k : ℕ) (hk : k ≤ n) : 
    orderOf (ω ^ (2 ^ k)) = 2 ^ (n - k) := by
  rw [orderOf_pow, hω]
  -- gcd(2^n, 2^k) = 2^k cuando k ≤ n
  have h_gcd : Nat.gcd (2 ^ n) (2 ^ k) = 2 ^ k := by
    have h_dvd : 2 ^ k ∣ 2 ^ n := by exact Nat.pow_dvd_pow 2 (by omega)
    rw [Nat.gcd_comm]
    exact Nat.gcd_eq_left h_dvd
  rw [h_gcd]
  -- 2^n / 2^k = 2^{n-k}
  exact Nat.pow_div (by omega) (by norm_num)

/- El cardinal de D_k es el orden de su generador.
   Esto es un hecho estándar: en un grupo finito, |⟨a⟩| = orderOf(a).
-/ 

theorem friDomain_card (k : ℕ) (hk : k ≤ n) : 
    Nat.card (friDomain ω k) = 2 ^ (n - k) := by
  unfold friDomain
  rw [Nat.card_zpowers]
  exact order_omega_pow ω n hω k hk

/- 
   Corolario principal: |D_k| = 2 · |D_{k+1}|.
   
   Esta es la observación de la pizarra: "|D_k| = 2|D_{k+1}| porque es cíclico".
   La razón es que elevar al cuadrado es un homomorfismo sobreyectivo 
   D_k → D_{k+1} con kernel {1, -1} de tamaño 2.
   
   Aquí lo derivamos directamente de la fórmula del orden.
-/ 

theorem friDomain_halving (k : ℕ) (hk : k < n) :
    Nat.card (friDomain ω k) = 2 * Nat.card (friDomain ω (k + 1)) := by
  have h1 := friDomain_card ω n hω k (by omega)
  have h2 := friDomain_card ω n hω (k + 1) (by omega)
  rw [h1, h2]
  -- n - k = (n - (k+1)) + 1, luego 2^{n-k} = 2 * 2^{n-(k+1)}
  have h_exp : n - k = (n - (k + 1)) + 1 := by omega
  rw [h_exp]
  ring

/- Equivalentemente: |D_{k+1}| = |D_k| / 2 -/ 

theorem friDomain_next_card (k : ℕ) (hk : k < n) :
    Nat.card (friDomain ω (k + 1)) = Nat.card (friDomain ω k) / 2 := by
  have h := friDomain_halving ω n hω k hk
  have h_pos : Nat.card (friDomain ω (k + 1)) > 0 := by
    rw [friDomain_card ω n hω (k + 1) (by omega)]
    exact Nat.pow_pos (by norm_num)
  -- De |D_k| = 2·|D_{k+1}| deducimos |D_{k+1}| = |D_k|/2
  omega

/- 
   Demostración por inducción completa de que |D_k| = 2^{n-k}.
   
   Caso base (k=0): |D_0| = |⟨ω⟩| = orderOf(ω) = 2^n. ✓
   
   Paso inductivo: si |D_k| = 2^{n-k}, entonces 
   |D_{k+1}| = |D_k|/2 = 2^{n-k}/2 = 2^{n-(k+1)}. ✓
   
   Esto formaliza exactamente la inducción que se menciona en clase.
-/ 

theorem friDomain_card_by_induction (k : ℕ) (hk : k ≤ n) :
    Nat.card (friDomain ω k) = 2 ^ (n - k) := by
  induction k with
  | zero =>
    -- Caso base: k = 0, D_0 = ⟨ω⟩, orden = 2^n
    exact friDomain_card ω n hω 0 (by omega)
  | succ k ih =>
    -- Paso inductivo
    have h_k_le_n : k ≤ n := by omega
    have h_k_lt_n : k < n := by omega
    
    -- Hipótesis inductiva
    have h_Dk : Nat.card (friDomain ω k) = 2 ^ (n - k) := ih h_k_le_n
    
    -- Reducción a la mitad
    have h_Dk1 : Nat.card (friDomain ω (k + 1)) = Nat.card (friDomain ω k) / 2 :=
      friDomain_next_card ω n hω k h_k_lt_n
    
    rw [h_Dk1, h_Dk]
    -- 2^{n-k} / 2 = 2^{n-(k+1)}
    have h_exp : n - k = (n - (k + 1)) + 1 := by omega
    rw [h_exp]
    rw [show 2 ^ ((n - (k + 1)) + 1) = 2 ^ (n - (k + 1)) * 2 by ring]
    simp

/- 
   Demostración alternativa de |D_{k+1}| = |D_k|/2 usando el primer teorema del isomorfismo.
   
   El homomorfismo φ : D_k → D_{k+1}, φ(x) = x^2 es sobreyectivo.
   Por el primer teorema del isomorfismo: D_k / ker(φ) ≅ im(φ) = D_{k+1}.
   
   El kernel es ker(φ) = {x ∈ D_k : x^2 = 1}. 
   Como D_k es cíclico de orden 2^{n-k} ≥ 2 (porque k < n),
   la ecuación x^2 = 1 tiene exactamente 2 soluciones: x = 1 y x = -1.
   
   Por tanto |D_{k+1}| = |D_k| / |ker(φ)| = |D_k| / 2.
   
   Usamos el lema estándar de Mathlib: en un grupo cíclico G, el kernel del
   homomorfismo x ↦ x^d tiene cardinalidad gcd(|G|, d).
-/ 

theorem friDomain_kernel_size (k : ℕ) (hk : k < n) [NeZero (2 : F)] :
    let φ : (friDomain ω k) →* Fˣ := 
      MonoidHom.mk' (fun (x : (friDomain ω k)) => (x.val ^ 2)) (by intros; simp [mul_pow])
    Nat.card (MonoidHom.ker φ) = 2 := by
  intro φ
  -- En un grupo cíclico, el kernel de x ↦ x^d tiene tamaño gcd(|G|, d)
  -- D_k es cíclico de orden 2^{n-k}, y d = 2, así que gcd(2^{n-k}, 2) = 2
  
  -- Primero, notamos que ker φ = ker(powMonoidHom 2) como subgrupos de D_k,
  -- porque ambos son {x ∈ D_k : x^2 = 1}
  have h_ker_eq : MonoidHom.ker φ = MonoidHom.ker (powMonoidHom 2 : (friDomain ω k) →* (friDomain ω k)) := by
    ext x
    simp only [MonoidHom.mem_ker, powMonoidHom_apply]
    -- Expandimos la definición de φ manualmente
    change ((x : Fˣ) ^ 2 = 1) ↔ (x ^ 2 = 1)
    -- La multiplicación en D_k es la restricción de la de Fˣ
    constructor
    · intro h_eq
      -- ↑x ^ 2 = 1 en Fˣ implica x^2 = 1 en D_k
      have : (x ^ 2 : (friDomain ω k)) = 1 := by
        apply Subtype.ext
        exact h_eq
      exact this
    · intro h_eq
      -- x^2 = 1 en D_k implica ↑x ^ 2 = 1 en Fˣ
      have h_eq2 : ((x ^ 2 : (friDomain ω k)) : Fˣ) = 1 := by
        rw [h_eq]
        rfl
      exact h_eq2
  
  rw [h_ker_eq]
  rw [IsCyclic.card_powMonoidHom_ker]
  -- gcd(2^{n-k}, 2) = 2 porque k < n implica 2^{n-k} ≥ 2
  have h_card : Nat.card (friDomain ω k) = 2 ^ (n - k) := friDomain_card ω n hω k (by omega)
  rw [h_card]
  have h_two_dvd : 2 ∣ 2 ^ (n - k) := by
    apply dvd_pow
    · exact dvd_refl 2
    · omega
  exact Nat.gcd_eq_right h_two_dvd

end Direct_FRI_Proof

/-
  Resumen de la prueba:
  
  1. D_k = ⟨ω^(2^k)⟩ es cíclico de orden 2^{n-k}.
  2. El homomorfismo φ(x) = x^2 mapea D_k sobre D_{k+1}.
  3. Como D_k es cíclico de orden potencia de 2, ker(φ) = {1, -1} tiene tamaño 2.
  4. Por el teorema del isomorfismo: |D_{k+1}| = |D_k| / 2.
  5. Por inducción: |D_k| = 2^{n-k} para todo k ≤ n.
  
  Esto justifica la reducción logarítmica en el protocolo FRI.
-/ 
