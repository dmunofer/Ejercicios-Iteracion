Algoritmo 10: definición del predicado es_un_número_válido — Versión 3 iterativa

es_un_número_válido(ca : CADENA ; BASE : ENTERO) : BOOLEANO
    # ¿`ca' representa un número válido en base `BASE'?

Precondición
    ca ≠ NULO
    longitud(ca) > 0
    1 < BASE < 37

constante
    I_MIN : ENTERO ← índice_min(ca)
    I_MAX : ENTERO ← índice_max(ca)

variable
    i : ENTERO # El índice del último carácter verificado

inicialización
    i ← I_MIN
    Resultado ← es_una_cifra_válida(ítem(ca, i), BASE))
    afirmación
        Resultado = 
          es_un_número_válido(sub_cadena(ca, I_MIN, i), BASE)

realización
    mientras que
        i < I_MAX y Resultado = VERDADERO
        invariante
            Resultado = 
                  es_un_número_válido
                              (sub_cadena(ca, I_MIN, i), BASE)
        variante de control
            I_MAX – i 

    repetir
        afirmación
            Resultado = es_un_número_válido
                   (
                     sub_cadena(ca, I_MIN, i), BASE)
                   )
        i ← i+1
        afirmación
            Resultado = es_un_número_válido
                   (
                     sub_cadena(ca, I_MIN, i-1), BASE)
                   )

        Resultado ← es_una_cifra_válida(ítem(ca,i), BASE)
        afirmación
            Resultado = es_un_número_válido
                   (
                     sub_cadena(ca, I_MIN, i), BASE)
                   )

    fin repetir

postcondición
    longitud(ca) = 1 => Resultado =
            es_una_cifra_válida(primero(ca), BASE)
    longitud(ca) > 1 => Resultado =
            es_una_cifra_válida(primero(ca), BASE)
          y entonces
            es_un_número_válido(fin(ca), BASE)

fin es_un_número_válido


Algoritmo 11: especificaciones de la función cadena_en_número

cadena_en_número(ca : CADENA ; BASE : ENTERO) : ENTERO
    # El entero que representa `ca' expresada en base `BASE'.

Precondición
    ca ≠ NULO
    longitud(ca) > 0
    1 < BASE < 37
    es_un_número_válido(ca, BASE)

postcondición
    ca = conversión2(Resultado, BASE)

fin cadena_en_número


Algoritmo 12: realización de la función cadena_en_número

...
constante
    I_MIN : ENTERO ← índice_min(ca)
    I_MAX : ENTERO ← índice_max(ca)

variable
    i : ENTERO 
        # El índice en `ca' del siguiente carácter a convertir
    cifra : CARACTER # Una cifra a convertir
    número  : ENTERO    # El número representado por cifra

inicialización
    i ← I_MIN
    Resultado ← 0

realización
    mientras que i ≤ I_MAX repetir
        cifra ← ítem(ca, i)
        número ← cifra_en_número(cifra, BASE)

        Resultado ← Resultado x BASE + número

        i ← i + 1
    fin repetir


Algoritmo 13: definición de la función cifra_en_número

cifra_en_número(cifra : CARACTER ; BASE : ENTERO) : ENTERO
    # El número que representa `cifra' en base `BASE'.

Precondición
    1 < BASE < 37
    es_una_cifra_válida(cifra, BASE)

constante
    CERO : ENTERO ← código('0')
    NUEVE : ENTERO ← código('9')
       A : ENTERO ← código('A')

variable
    código_cifra : ENTERO

realización
    código_cifra ← código(cifra)
    si
      CERO ≤ código_cifra ≤ NUEVE
    entonces
      Resultado ← código_cifra – CERO
    si no
      Resultado ← código_cifra – (A – 10)
    fin si

postcondición
    código('0') ≤ código(cifra) ≤ código('9') =>
                     Resultado = código(cifra) – código('0')
    código('9') < código(cifra) =>
                     Resultado = código(cifra) – código('A') + 10

fin cifra_en_número
