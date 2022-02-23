Algoritmo : Realización de la función índice_palabra 

variable
    i, j : ENTERO

inicialización
    i ← inicio
        # Índice de la siguiente celda a observar
    j ← siguiente[i]
        # Índice de la palabra que sigue a la de índice i en orden
    Resultado ← AUSENTE
    
realización
    mientras que
        ítem(diccionario[i], 1) < inicial y entonces j ≠ INFINITO
        invariante
            se han observado las palabras de índice inicio, 
            siguiente[inicio],…,anterior[i]. Resultado = AUSENTE
            j = siguiente[i]
        variante de control
            ???
    repetir
        afirmación
            se han observado las palabras de índice inicio, 
            siguiente[inicio],…,anterior[i] e i. Resultado = AUSENTE

        i ← j
        afirmación
            se han observado las palabras de índice inicio, 
            siguiente[inicio], …,anterior[i]. Resultado = AUSENTE
            j = i

        j ← siguiente[i]
        afirmación
            se han observado las palabras de índice inicio, 
            siguiente[inicio], …,anterior[i]. Resultado = AUSENTE
            j = siguiente[i]
    fin repetir

    # ítem(diccionario[i], 1) ≥ inicial o si no j = INFINITO:
    #
    # ítem(diccionario[i], 1) > inicial o si no j = INFINITO =>
    # Resultado = AUSENTE
    # ítem(diccionario[i], 1) = inicial => Resultado ≠ AUSENTE
    si
        ítem(diccionario[i], 1) = inicial
    entonces
        Resultado ← i
    fin si
...

tipo PALABRA estructura
    anterior : ENTERO
        # El índice de la palabra que precede a esta palabra
    siguiente   : ENTERO
        # El índice de la palabra siguiente
    palabra : CADENA
fin PALABRA


Algoritmo: Definición del procedimiento inicializar

inicializar(diccionario : TABLA[PALABRA])
    # Inicializa un `diccionario' vacío.

Precondición
    está_definido(diccionario)

constante
    INFINITO : PALABRA
        # La mayor palabra de todas
    I_MIN : ENTERO ← índice_min(diccionario)
    I_MAX : ENTERO ← índice_max(diccionario)

variable
    i : ENTERO    # Índice de la siguiente celda a inicializar

inicialización
    i ← I_MIN     # Índice de la siguiente celda a liberar

realización
    # La primera celda contiene «la mayor palabra»
    diccionario[I_MIN].palabra ← INFINITO

    # Todas las celdas se indexan por sí mismas : tabla vacía
    mientras que i ≤ I_MAX repetir
        diccionario[i].anterior ← i
        diccionario[i].siguiente ← i
        i ← i + 1
    fin repetir

postcondición
    # El diccionario está vacío
    está_libre(diccionario)

fin inicializar

Algoritmo 8: Definición del predicado está_libre

está_libre(diccionario : TABLA[PALABRA])
    # ¿`diccionario' está vacío de palabra?

Precondición
    está_definido(diccionario)

constante
    I_MIN : ENTERO ← índice_min(diccionario)
    I_MAX : ENTERO ← índice_max(diccionario)

variable
    i : ENTERO # Índice de la siguiente celda a verificar

inicialización
    i ← I_MIN  # Índice de la siguiente celda a verificar
    Resultado ← VERDADERO

realización
    # ¿Todas las celdas se indexan a sí mismas?
    mientras que i ≤ I_MAX y entonces Resultado = VERDADERO repetir
        Resultado ← (diccionario[i].anterior = i y 
                   diccionario[i].siguiente = i)
        i ← i + 1
    fin repetir

postcondición
    # Ninguna palabra en la tabla : el diccionario está vacío
    está_vacío(diccionario)

    # Ninguna celda ocupada
    (∀k ∈ ℤ)
    (índice_min(diccionario) < k ≤ índice_max(diccionario) =>
    diccionario[k].anterior = diccionario[k].siguiente = k)

fin está_libre

Algoritmo : Definición del procedimiento insertar

insertar
    (
      k : ENTERO ;
      diccionario : TABLA[PALABRA] ;
      situación : ENTERO
    )
    # Insertar la palabra de índice `k' delante `diccionario[situación]'.

Precondición
    está_definido(diccionario)
    índice_válido(diccionario, k)
    índice_válido(diccionario, situación)

variable
    anterior : ENTERO # Copia de seguridad de un índice

realización
    # Inserción de palabra_3 entre palabra_1 y palabra_2

    # Copia de seguridad del enlace de palabra_2 hacia palabra_1
    anterior ← diccionario[situación].anterior # 0:s

    # Enlace de palabra_1 hacia palabra_3
    diccionario[anterior].siguiente ← k   # 1

    # enlaces de palabra_3 hacia palabra_1 y palabra_2
    diccionario[k].anterior ← anterior # 2
    diccionario[k].siguiente ← situación    # 3

    # enlace de palabra_2 hacia palabra_3
    diccionario[situación].anterior ← k  # 4 

fin insertar


Algoritmo 10: Definición del procedimiento de eliminación de una palabra

eliminación(ca : CADENA ; diccionario : TABLA[PALABRA])
    # Elimina `ca' del `diccionario'.

Precondición
    ca ≠ NULO
    está_definido(diccionario)
    no está_vacío(diccionario)


constante
    I_MIN : ENTERO ← índice_min(diccionario)
    I_MAX : ENTERO ← índice_max(diccionario)

variable
    situación : ENTERO # El índice de la palabra a eliminar

realización
    situación ← índice_palabra(ca, diccionario)
    si
        situación ≠ AUSENTE
    entonces
        eliminar(diccionario, situación)
    fin si

postcondición
    antiguo(ca) = ca
    La palabra de valor `ca' se ha eliminado de `diccionario'

fin eliminación
