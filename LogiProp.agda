open import Data.Product renaming (_×_ to _∧_)

--{ A lo largo de este documento, pensaremos que los tipos corresponden a
    proposiciones matemáticas, mientras que los términos de los tipos
    corresponden a demostraciones matemáticas.

    De forma interna, Agda emplea universos de tipos, siento Set = Set₀ el más
    pequeño. En espíritu de nuestra semántica con base en la Teoría Homotópica
    de Tipos

--{ Tipos algebraicos }--
--{ Tipo Producto }--

--{ En la primera línea, donde se hizo el import de la stdlib, importamos
    la definición del tipo producto en Agda.
    Además, podemos renombrar el operador. Pensando en la correspondencia
    Curry-Howard-Lambek, identificamos el producto con la conjunción lógica.
}--

--{ Afirmación: La conjunción es conmutativa. }--






--{ Esto es sólo notación mía. }-
--{ En Agda, Set es un tipo truncado Type_1 }--

Type = Set

-- Definiciones de tipos

