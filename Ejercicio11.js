Algoritmo 1: Especificaciones de la función mcd

mcd(n, m : ENTERO) : ENTERO
    # El Máximo Común Divisor de `n' y `m'.

precondición
    # Enteros naturales
    n ≥ 0 ; m ≥ 0

    # 0 no tiene máximo divisor
    n ≠ 0 o si no m ≠ 0

postcondición
    # El MCD divide `n' y `m'
    resto(n, Resultado) = 0
    resto(m, Resultado) = 0

    # Es el número entero máximo que tiene esta propiedad
    (∀k ∈ ℕ)(n ≠ 0 o si no m ≠ 0)
        (k > Resultado => resto(n, k) ≠ 0 o si no resto(m, k) ≠ 0)

fin mcd


Algoritmo 2: Realización de la función mcd – Versión 1

mcd(n, m : ENTERO) : ENTERO
    # El Máximo Común Divisor de `n' y `m'.

precondición
    # Enteros naturales
    n ≥ 0 ; m ≥ 0

    # 0 no tiene máximo divisor
    n ≠ 0 o si no m ≠ 0

variable
    dividendo, divisor, resto : ENTERO

inicialización
    divisor ← n
    resto ← m

realización
    mientras que
        resto > 0
        invariante
            (H): la última división de la serie ha utilizado el
                  resto de la división anterior como divisor y
                  ha dado resto como resultado.
        variante de control
            resto
    repetir
        afirmación
            resto > 0
        # Preparar la siguiente división
        dividendo ← divisor
        divisor  ← resto

        # Calcular el siguiente resto
        resto ← dividendo modulo divisor
        afirmación
            (H) : la última división de la serie ha utilizado el
                  resto de la división anterior como divisor y
                  ha dado resto como resultado.        
    fin repetir
    afirmación
        resto = 0

    # El resultado es el último resto no nulo
    Resultado ← divisor

postcondición
    # El MCD divide `n' y `m'
    resto(n, Resultado) = 0
    resto(m, Resultado) = 0

    # Es el máximo entero que tiene esta propiedad
    (∀k ∈ ℕ)(n ≠ 0 o si no m ≠ 0)
        (k > Resultado => resto(n, k) ≠ 0 o si no resto(m, k) ≠ 0)

fin mcd


Algoritmo 3: resto_2 de la división euclidiana de dos enteros — Versión solo con sumas

resto_2(a, b : ENTERO) : ENTERO
    # El resto de la división euclidiana de `a' por `b'.
    #
    # b x q ≤ a < b x (q+1) y r = a — b x q => 
    # a — b x (q+1) < 0 et r = a — b x (q+1) + b

precondición
    a ≥ 0 ; b > 0

inicialización
    Resultado ← a

realización
    repetir
        Resultado ← Resultado – b
    hasta que
        Resultado < 0
    fin repetir
    afirmación
        Resultado = a — b x (cociente(a, b) + 1)

    Resultado ← Resultado + b
    afirmación
        Resultado = a — b x (cociente(a, b) + 1) + b => 
        Resultado = a — b x  cociente(a, b)

postcondición
    Resultado = a – b x cociente(a, b)

fin resto_2


