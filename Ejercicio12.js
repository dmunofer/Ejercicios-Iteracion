Algoritmo 1: función tabla_de_los_cuadrados – Versión 1

Algoritmo tabla_de_los_cuadrados
	# La serie en `cuadrados' de los cuadrados perfectos inferiores
	# a `límite'.

Entrada
	cuadrados : TABLEAU[ENTERO]	# La tabla a inicializar
	límite : ENTERO # El límite superior de los cuadrados a calcular

precondición
	límite ≥ 0
	límite ≤ índice_max(cuadrados) x índice_max(cuadrados)

variable
	 cuadrado : ENTERO	# Un cuadrado perfecto k2
	impar : ENTERO	# Un impar de la suite 2xk + 1

inicialización
	     k ← 0	# el entero para el que se calcula el cuadrado
	 cuadrado ← 0	# cuadrado  = k2
	impar ← 1	# impar = 2xk + 1

realización
	hasta que
		cuadrado > límite
	repetir
		cuadrados[k] ← cuadrado
		cuadrado ← cuadrado + impar
		impar ← impar + 2
		k ← k +1
	fin repetir

postcondición
	antiguo(límite) = límite

	(∀k ∈ ℤ)(índice_min(cuadrados) ≤ k et k2 ≤ límite =>	
		   cuadrados[k] = k2 )
		
fin tabla_de_los_cuadrados


Algoritmo 4: Raíz cuadrada entera de un número entero positivo – Versión 1

algoritmo raíz_cuadrada_entera
	# La raíz cuadrada entera del número entero `n'.

Entrada
	     n : ENTERO		# cálculo de entero()
	cuadrados : TABLA[ENTERO]	# La tabla de los cuadrados perfectos
	raíz : ENTERO		# entero()

precondición
	n ≥ 0

postcondición
	# El número entero `n' no se ha modificado
	antiguo(n) = n

	# Las celdas de la tabla inicial no se han modificado
	antiguo	(
		sub_tabla(cuadrados,
				antiguo(índice_min(cuadrados)) + 1,
				antiguo(cuadrados[índice_min(cuadrados)])
		            )
	       )
		=
		sub_tabla(cuadrados,
				índice_min(cuadrados) + 1, 
				antiguo(cuadrados[índice_min(cuadrados)])
		            )

	# La tabla se amplía si es insuficiente
	cuadrados[antiguo(índice_min(cuadrados))] < n => 
					cuadrados[índice_min(cuadrados)] ≥ n

	# Si no, no se modifican ni la tabla ni índice_min(cuadrados)
	cuadrados[antiguo(índice_min(cuadrados))] ≥ n => 
	antiguo(índice_min(cuadrados)) = índice_min(cuadrados)

	# `raíz' es la raíz cuadrada entera de `n'
	raíz2 ≤ n < (raíz + 1)2 <=> raíz = []

fin raíz_cuadrada_entera
