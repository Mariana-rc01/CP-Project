\documentclass[11pt, a4paper, fleqn]{article}
\usepackage{cp2425t}
\makeindex

%================= lhs2tex=====================================================%
%include polycode.fmt
%format (div (x)(y)) = x "\div " y
%format succ = "\succ "
%format ==> = "\Longrightarrow "
%format map = "\map "
%format length = "\length "
%format fst = "\p1"
%format p1  = "\p1"
%format snd = "\p2"
%format p2  = "\p2"
%format Left = "i_1"
%format Right = "i_2"
%format i1 = "i_1"
%format i2 = "i_2"
%format >< = "\times"
%format >|<  = "\bowtie "
%format |-> = "\mapsto"
%format . = "\comp "
%format .=?=. = "\mathbin{\stackrel{\mathrm{?}}{=}}"
%format (kcomp (f)(g)) = f "\kcomp " g
%format -|- = "+"
%format conc = "\mathsf{conc}"
%format summation = "{\sum}"
%format (either (a) (b)) = "\alt{" a "}{" b "}"
%format (frac (a) (b)) = "\frac{" a "}{" b "}"
%format (uncurry f) = "\uncurry{" f "}"
%format (const (f)) = "\underline{" f "}"
%format TLTree = "\mathsf{TLTree}"
%format (Seq (a)) = "{" a "}^{*}"
%format (lcbr (x)(y)) = "\begin{lcbr}" x "\\" y "\end{lcbr}"
%format (lcbr3 (x)(y)(z)) = "\begin{lcbr}" x "\\" y "\\" z "\end{lcbr}"
%format (split (x) (y)) = "\conj{" x "}{" y "}"
%format (for (f) (i)) = "\for{" f "}\ {" i "}"
%format B_tree = "\mathsf{B}\mbox{-}\mathsf{tree} "
%format <$> = "\mathbin{\mathopen{\langle}\$\mathclose{\rangle}}"
%format Either a b = a "+" b
%format fmap = "\mathsf{fmap}"
%format NA   = "\textsc{na}"
%format NB   = "\textbf{NB}"
%format inT = "\mathsf{in}"
%format outT = "\mathsf{out}"
%format outLTree = "\mathsf{out}"
%format inLTree = "\mathsf{in}"
%format inFTree = "\mathsf{in}"
%format outFTree = "\mathsf{out}"
%format Null = "1"
%format (Prod (a) (b)) = a >< b
%format fF = "\fun F "
%format l2 = "l_2 "
%format Dist = "\fun{Dist}"
%format IO = "\fun{IO}"
%format LTree = "{\LTree}"
%format FTree = "{\FTree}"
%format inNat = "\mathsf{in}"
%format (cata (f)) = "\llparenthesis\, " f "\,\rrparenthesis"
%format (cataNat (g)) = "\cataNat{" g "}"
%format (cataList (g)) = "\llparenthesis\, " g "\,\rrparenthesis"
%format (cataLTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (cataFTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (cataRose (x)) = "\llparenthesis\, " x "\,\rrparenthesis_\textit{\tiny R}"
%format (ana (g)) = "\ana{" g "}"
%format (anaList (g)) = "\anaList{" g "}"
%format (anaLTree (g)) = "\lanabracket\," g "\,\ranabracket"
%format (anaRose (g)) = "\lanabracket\," g "\,\ranabracket_\textit{\tiny R}"
%format (hylo (g) (h)) = "\llbracket\, " g ",\," h "\,\rrbracket"
%format (hyloRose (g) (h)) = "\llbracket\, " g ",\," h "\,\rrbracket_\textit{\tiny R}"
%format Nat0 = "\N_0"
%format Rational = "\Q "
%format toRational = " to_\Q "
%format fromRational = " from_\Q "
%format muB = "\mu "
%format (frac (n)(m)) = "\frac{" n "}{" m "}"
%format (fac (n)) = "{" n "!}"
%format (underbrace (t) (p)) = "\underbrace{" t "}_{" p "}"
%format matrix = "matrix"
%format `ominus` = "\mathbin{\ominus}"
%format % = "\mathbin{/}"
%format <-> = "{\,\leftrightarrow\,}"
%format <|> = "{\,\updownarrow\,}"
%format `minusNat`= "\mathbin{-}"
%format ==> = "\Rightarrow"
%format .==>. = "\Rightarrow"
%format .<==>. = "\Leftrightarrow"
%format .==. = "\equiv"
%format .<=. = "\leq"
%format .&&&. = "\wedge"
%format cdots = "\cdots "
%format pi = "\pi "
%format (curry (f)) = "\overline{" f "}"
%format delta = "\Delta "
%format (plus (f)(g)) = "{" f "}\plus{" g "}"
%format ++ = "\mathbin{+\!\!+}"
%format Integer  = "\mathbb{Z}"
%format (Cp.cond (p) (f) (g)) = "\mcond{" p "}{" f "}{" g "}"
%format (square (x)) = x "^2"

%format (cataTree (f) (g)) = "\llparenthesis\, " f "\:" g "\,\rrparenthesis_{\textit{\tiny T}}"
%format (cataForest (f) (g)) = "\llparenthesis\, " f "\:" g "\,\rrparenthesis_{\textit{\tiny F}}"
%format (anaTree (f) (g)) = "\lanabracket\;\!" f "\:" g "\:\!\ranabracket_{\textit{\tiny T}}"
%format (anaForest (f) (g)) = "\lanabracket\;\!" f "\:" g "\:\!\ranabracket_{\textit{\tiny F}}"
%format (hyloTree (ft) (ff) (gt) (gf)) = "\llbracket\, " ft "\:" ff ",\," gt "\:" gf "\,\rrbracket_{\textit{\tiny T}}"
%format (hyloForest (ft) (ff) (gt) (gf)) = "\llbracket\, " ft "\:" ff ",\," gt "\:" gf "\,\rrbracket_{\textit{\tiny F}}"
%format inTree = "\mathsf{in}_{Tree}"
%format inForest = "\mathsf{in}_{Forest}"
%format outTree = "\mathsf{out}_{Tree}"
%format outForest = "\mathsf{out}_{Forest}"

%format (cata' (f) (g)) = "\llparenthesis\, " f "\:" g "\,\rrparenthesis"
%format (ana' (f) (g)) = "\lanabracket\;\!" f "\:" g "\:\!\ranabracket"
%format (hylo' (ft) (ff) (gt) (gf)) = "\llbracket\, " ft "\:" ff ",\," gt "\:" gf "\,\rrbracket"
%format .* = "\star " 
%------------------------------------------------------------------------------%


%====== DEFINIR GRUPO E ELEMENTOS =============================================%

\group{G2}
\studentA{104356}{João d'Araújo Dias Lobo }
\studentB{90817}{Mariana Rocha Cristino }
\studentC{104439}{Rita da Cunha Camacho }

%==============================================================================%

\begin{document}

\sffamily
\setlength{\parindent}{0em}
\emergencystretch 3em
\renewcommand{\baselinestretch}{1.25} 
\input{Cover}
\pagestyle{pagestyle}
\setlength{\parindent}{1em}
\newgeometry{left=25mm,right=20mm,top=25mm,bottom=25mm}

\section*{Preâmbulo}

Em \CP\ pretende-se ensinar a progra\-mação de computadores como uma disciplina
científica. Para isso parte-se de um repertório de \emph{combinadores} que
formam uma álgebra da programação % (conjunto de leis universais e seus corolários)
e usam-se esses combinadores para construir programas \emph{composicionalmente},
isto é, agregando programas já existentes.

Na sequência pedagógica dos planos de estudo dos cursos que têm esta disciplina,
opta-se pela aplicação deste método à programação em \Haskell\ (sem prejuízo
da sua aplicação a outras linguagens funcionais). Assim, o presente trabalho
prático coloca os alunos perante problemas concretos que deverão ser implementados
em \Haskell. Há ainda um outro objectivo: o de ensinar a documentar programas,
a validá-los e a produzir textos técnico-científicos de qualidade.

Antes de abordarem os problemas propostos no trabalho, os grupos devem ler
com atenção o anexo \ref{sec:documentacao} onde encontrarão as instruções
relativas ao \emph{software} a instalar, etc.

Valoriza-se a escrita de \emph{pouco} código que corresponda a soluções simples
e elegantes que utilizem os combinadores de ordem superior estudados na disciplina.

%if False
\begin{code}
{-# OPTIONS_GHC -XNPlusKPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances, UndecidableInstances #-}
module Main where
import Cp
import List hiding (fac)
import Nat hiding (aux)
import LTree
import FTree
import Exp
-- import Probability
import Data.List hiding (find)
-- import Svg hiding (for,dup,fdiv)
import Control.Monad
import Control.Applicative hiding ((<|>))
import System.Process
import Data.Char
import Data.Ratio
import Control.Concurrent
import Data.List (find)
import BTree (hyloBTree, qsep)

main = undefined
\end{code}
%endif

\Problema

Esta questão aborda um problema que é conhecido pela designação '\emph{H-index of a Histogram}'
e que se formula facilmente:
\begin{quote}\em
O h-index de um histograma é o maior número |n| de barras do histograma cuja altura é maior ou igual a |n|.
\end{quote}
Por exemplo, o histograma 
\begin{code}
h = [5,2,7,1,8,6,4,9]
\end{code}
que se mostra na figura
	\histograma
tem |hindex h = 5|
pois há |5| colunas maiores que |5|. (Não é |6| pois maiores ou iguais que seis só há quatro.)

Pretende-se definida como um catamorfismo, anamorfismo ou hilomorfismo uma função em Haskell
\begin{code}
hindex :: [Int] -> (Int,[Int])
\end{code}
tal que, para |(i,x) = hindex h|, |i| é o H-index de |h| e |x| é a lista de colunas de |h| que para ele contribuem.

A proposta de |hindex| deverá vir acompanhada de um \textbf{diagrama} ilustrativo.

\Problema

Pelo \href{https://en.wikipedia.org/wiki/Fundamental_theorem_of_arithmetic}{teorema
fundamental da aritmética}, todo número inteiro positivo tem uma única factorização
prima.  For exemplo,
\begin{verbatim}
primes 455
[5,7,13]
primes 433
[433]
primes 230
[2,5,23]
\end{verbatim}

\begin{enumerate}

\item	
Implemente como anamorfismo de listas a função
\begin{code}
primes :: Integer -> [Integer] 
\end{code}
que deverá, recebendo um número inteiro positivo, devolver a respectiva lista
de factores primos.

A proposta de |primes| deverá vir acompanhada de um \textbf{diagrama} ilustrativo.

\item A figura mostra a ``\emph{árvore dos primos}'' dos números |[455,669,6645,34,12,2]|.

      \primes

Com base na alínea anterior, implemente uma função em Haskell que faça a
geração de uma tal árvore a partir de uma lista de inteiros:

\begin{code}
prime_tree :: [Integer] -> Exp Integer Integer
\end{code}

\textbf{Sugestão}: escreva o mínimo de código possível em |prime_tree| investigando
cuidadosamente que funções disponíveis nas bibliotecas que são dadas podem
ser reutilizadas.%
\footnote{Pense sempre na sua produtividade quando está a programar --- essa
atitude será valorizada por qualquer empregador que vier a ter.}

\end{enumerate}

\Problema

A convolução |a .* b| de duas listas |a| e |b| --- uma operação relevante em computação
---  está muito bem explicada
\href{https://www.youtube.com/watch?v=KuXjwB4LzSA}{neste vídeo} do canal
\textbf{3Blue1Brown} do YouTube,
a partir de \href{https://www.youtube.com/watch?v=KuXjwB4LzSA&t=390s}{|t=6:30|}.
Aí se mostra como, por exemplo:
\begin{quote}
|[1,2,3] .* [4,5,6] = [4,13,28,27,18]| 
\end{quote}
A solução abaixo, proposta pelo chatGPT,
\begin{spec}
convolve :: Num a => [a] -> [a] -> [a]
convolve xs ys = [sum $ zipWith (*) (take n (drop i xs)) ys | i <- [0..(length xs - n)]]
  where n = length ys 
\end{spec}
está manifestamente errada, pois |convolve [1,2,3] [4,5,6] = [32]| (!).

Proponha, explicando-a devidamente, uma solução sua para |convolve|.
Valorizar-se-á a economia de código e o recurso aos combinadores \emph{pointfree} estudados
na disciplina, em particular a triologia \emph{ana-cata-hilo} de tipos disponíveis nas
bibliotecas dadas ou a definir.

\Problema

Considere-se a seguinte sintaxe (abstrata e simplificada) para \textbf{expressões numéricas} (em |b|) com variáveis (em |a|),
\begin{code}
data Expr b a =   V a | N b | T Op [ Expr b a ]  deriving (Show,Eq)

data Op = ITE | Add | Mul | Suc deriving (Show,Eq)
\end{code}
possivelmente condicionais (cf.\ |ITE|, i.e.\ o operador condicional ``if-then-else``).
Por exemplo, a árvore mostrada a seguir
        \treeA
representa a expressão
\begin{eqnarray}
        |ite (V "x") (N 0) (multi (V "y") (soma (N 3) (V "y")))|
        \label{eq:expr}
\end{eqnarray}
--- i.e.\ |if x then 0 else y*(3+y)| ---
assumindo as ``helper functions'':
\begin{code}
soma  x y = T Add [x,y]
multi x y = T Mul [x,y]
ite x y z = T ITE [x,y,z]
\end{code}

No anexo \ref{sec:codigo} propôe-se uma base para o tipo Expr (|baseExpr|) e a 
correspondente algebra |inExpr| para construção do tipo |Expr|.

\begin{enumerate}
\item        Complete as restantes definições da biblioteca |Expr|  pedidas no anexo \ref{sec:resolucao}.
\item        No mesmo anexo, declare |Expr b| como instância da classe |Monad|. \textbf{Sugestão}: relembre os exercícios da ficha 12.
\item        Defina como um catamorfismo de |Expr| a sua versão monádia, que deverá ter o tipo:
\begin{code}
mcataExpr :: Monad m => (Either a (Either b (Op, m [c])) -> m c) -> Expr b a -> m c
\end{code}
\item        Para se avaliar uma expressão é preciso que todas as suas variáveis estejam instanciadas.
Complete a definição da função
\begin{code}
let_exp :: (Num c) => (a -> Expr c b) -> Expr c a -> Expr c b
\end{code}
que, dada uma expressão com variáveis em |a| e uma função que a cada uma dessas variáveis atribui uma
expressão (|a -> Expr c b|), faz a correspondente substituição.\footnote{Cf.\ expressões |let ... in ...|.}
Por exemplo, dada
\begin{code}
f "x" = N 0
f "y" = N 5
f _   = N 99
\end{code}
ter-se-á
\begin{spec}
        let_exp f e = T ITE [N 1,N 0,T Mul [N 5,T Add [N 3,N 1]]]
\end{spec}
isto é, a árvore da figura a seguir: 
        \treeB

\item Finalmente, defina a função de avaliação de uma expressão, com tipo

\begin{code}
evaluate :: (Num a, Ord a) =>  Expr a b -> Maybe a
\end{code}

que deverá ter em conta as seguintes situações de erro:

\begin{enumerate}

\item \emph{Variáveis} --- para ser avaliada, |x| em |evaluate x| não pode conter variáveis. Assim, por exemplo,
        \begin{spec}
        evaluate e = Nothing
        evaluate (let_exp f e) = Just 40
        \end{spec}
para |f| e |e|  dadas acima.

\item \emph{Aridades} --- todas as ocorrências dos operadores deverão ter
      o devido número de sub-expressões, por exemplo:
        \begin{spec}
        evaluate (T Add [ N 2, N 3]) = Just 5
        evaluate (T Mul [ N 2 ]) = Nothing
        \end{spec}

\end{enumerate}

\end{enumerate}

\noindent
\textbf{Sugestão}: de novo se insiste na escrita do mínimo de código possível,
tirando partido da riqueza estrutural do tipo |Expr| que é assunto desta questão.
Sugere-se também o recurso a diagramas para explicar as soluções propostas.

\part*{Anexos}

\appendix

\section{Natureza do trabalho a realizar}
\label{sec:documentacao}
Este trabalho teórico-prático deve ser realizado por grupos de 3 alunos.
Os detalhes da avaliação (datas para submissão do relatório e sua defesa
oral) são os que forem publicados na \cp{página da disciplina} na \emph{internet}.

Recomenda-se uma abordagem participativa dos membros do grupo em \textbf{todos}
os exercícios do trabalho, para assim poderem responder a qualquer questão
colocada na \emph{defesa oral} do relatório.

Para cumprir de forma integrada os objectivos do trabalho vamos recorrer
a uma técnica de programa\-ção dita ``\litp{literária}'' \cite{Kn92}, cujo
princípio base é o seguinte:
%
\begin{quote}\em
	Um programa e a sua documentação devem coincidir.
\end{quote}
%
Por outras palavras, o \textbf{código fonte} e a \textbf{documentação} de um
programa deverão estar no mesmo ficheiro.

O ficheiro \texttt{cp2425t.pdf} que está a ler é já um exemplo de
\litp{programação literária}: foi gerado a partir do texto fonte
\texttt{cp2425t.lhs}\footnote{O sufixo `lhs' quer dizer
\emph{\lhaskell{literate Haskell}}.} que encontrará no \MaterialPedagogico\
desta disciplina des\-com\-pactando o ficheiro \texttt{cp2425t.zip}.

Como se mostra no esquema abaixo, de um único ficheiro (|lhs|)
gera-se um PDF ou faz-se a interpretação do código \Haskell\ que ele inclui:

	\esquema

Vê-se assim que, para além do \GHCi, serão necessários os executáveis \PdfLatex\ e
\LhsToTeX. Para facilitar a instalação e evitar problemas de versões e
conflitos com sistemas operativos, é recomendado o uso do \Docker\ tal como
a seguir se descreve.

\section{Docker} \label{sec:docker}

Recomenda-se o uso do \container\ cuja imagem é gerada pelo \Docker\ a partir do ficheiro
\texttt{Dockerfile} que se encontra na diretoria que resulta de descompactar
\texttt{cp2425t.zip}. Este \container\ deverá ser usado na execução
do \GHCi\ e dos comandos relativos ao \Latex. (Ver também a \texttt{Makefile}
que é disponibilizada.)

Após \href{https://docs.docker.com/engine/install/}{instalar o Docker} e
descarregar o referido zip com o código fonte do trabalho,
basta executar os seguintes comandos:
\begin{Verbatim}[fontsize=\small]
    $ docker build -t cp2425t .
    $ docker run -v ${PWD}:/cp2425t -it cp2425t
\end{Verbatim}
\textbf{NB}: O objetivo é que o container\ seja usado \emph{apenas} 
para executar o \GHCi\ e os comandos relativos ao \Latex.
Deste modo, é criado um \textit{volume} (cf.\ a opção \texttt{-v \$\{PWD\}:/cp2425t}) 
que permite que a diretoria em que se encontra na sua máquina local 
e a diretoria \texttt{/cp2425t} no \container\ sejam partilhadas.

Pretende-se então que visualize/edite os ficheiros na sua máquina local e que
os compile no \container, executando:
\begin{Verbatim}[fontsize=\small]
    $ lhs2TeX cp2425t.lhs > cp2425t.tex
    $ pdflatex cp2425t
\end{Verbatim}
\LhsToTeX\ é o pre-processador que faz ``pretty printing'' de código Haskell
em \Latex\ e que faz parte já do \container. Alternativamente, basta executar
\begin{Verbatim}[fontsize=\small]
    $ make
\end{Verbatim}
para obter o mesmo efeito que acima.

Por outro lado, o mesmo ficheiro \texttt{cp2425t.lhs} é executável e contém
o ``kit'' básico, escrito em \Haskell, para realizar o trabalho. Basta executar
\begin{Verbatim}[fontsize=\small]
    $ ghci cp2425t.lhs
\end{Verbatim}

\noindent Abra o ficheiro \texttt{cp2425t.lhs} no seu editor de texto preferido
e verifique que assim é: todo o texto que se encontra dentro do ambiente
\begin{quote}\small\tt
\verb!\begin{code}!
\\ ... \\
\verb!\end{code}!
\end{quote}
é seleccionado pelo \GHCi\ para ser executado.

\section{Em que consiste o TP}

Em que consiste, então, o \emph{relatório} a que se referiu acima?
É a edição do texto que está a ser lido, preenchendo o anexo \ref{sec:resolucao}
com as respostas. O relatório deverá conter ainda a identificação dos membros
do grupo de trabalho, no local respectivo da folha de rosto.

Para gerar o PDF integral do relatório deve-se ainda correr os comando seguintes,
que actualizam a bibliografia (com \Bibtex) e o índice remissivo (com \Makeindex),
\begin{Verbatim}[fontsize=\small]
    $ bibtex cp2425t.aux
    $ makeindex cp2425t.idx
\end{Verbatim}
e recompilar o texto como acima se indicou. (Como já se disse, pode fazê-lo
correndo simplesmente \texttt{make} no \container.)

No anexo \ref{sec:codigo} disponibiliza-se algum código \Haskell\ relativo
aos problemas que são colocados. Esse anexo deverá ser consultado e analisado
à medida que isso for necessário.

Deve ser feito uso da \litp{programação literária} para documentar bem o código que se
desenvolver, em particular fazendo diagramas explicativos do que foi feito e
tal como se explica no anexo \ref{sec:diagramas} que se segue.

\section{Como exprimir cálculos e diagramas em LaTeX/lhs2TeX} \label{sec:diagramas}

Como primeiro exemplo, estudar o texto fonte (\lhstotex{lhs}) do que está a ler\footnote{
Procure e.g.\ por \texttt{"sec:diagramas"}.} onde se obtém o efeito seguinte:\footnote{Exemplos
tirados de \cite{Ol18}.}
\begin{eqnarray*}
\start
|
	id = split f g
|
\just\equiv{ universal property }
|
     lcbr(
          p1 . id = f
     )(
          p2 . id = g
     )
|
\just\equiv{ identity }
|
     lcbr(
          p1 = f
     )(
          p2 = g
     )
|
\qed
\end{eqnarray*}

Os diagramas podem ser produzidos recorrendo à \emph{package} \Xymatrix, por exemplo:
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Nat0|
           \ar[d]_-{|cataNat g|}
&
    |1 + Nat0|
           \ar[d]^{|id + (cataNat g)|}
           \ar[l]_-{|inNat|}
\\
     |B|
&
     |1 + B|
           \ar[l]^-{|g|}
}
\end{eqnarray*}

\section{Código fornecido}\label{sec:codigo}

\subsection*{Problema 1}

\begin{code}
h :: [Int]
\end{code}

\subsection*{Problema 4}
Definição do tipo:
\begin{code}
inExpr = either V (either N (uncurry T))

baseExpr g h f = g -|- (h -|- id >< map f)
\end{code}
Exemplos de expressões:
\begin{code}
e = ite (V "x") (N 0) (multi (V "y") (soma (N 3) (V "y")))
i = ite (V "x") (N 1) (multi (V "y") (soma (N (3%5)) (V "y")))
\end{code}
Exemplo de teste:
\begin{code}
teste = evaluate (let_exp f i) == Just (26 % 245)
    where f "x" = N 0 ; f "y" = N (1%7)
\end{code}

%----------------- Soluções dos alunos -----------------------------------------%

\section{Soluções dos alunos}\label{sec:resolucao}
Os alunos devem colocar neste anexo as suas soluções para os exercícios
propostos, de acordo com o ``layout'' que se fornece.
Não podem ser alterados os nomes ou tipos das funções dadas, mas pode ser
adicionado texto ao anexo, bem como diagramas e/ou outras funções auxiliares
que sejam necessárias.

\noindent
\textbf{Importante}: Não pode ser alterado o texto deste ficheiro fora deste anexo.

\subsection*{Problema 1}

A função |hindex| foi implementada como um hilomorfismo de |BTree| (|hyloBTree|), visto que o problema assemelha-se ao processo de ordenação |qsort|,
que também utiliza um hilomorfismo. A ideia principal foi usar a partição de elementos como o |qSort| usa e adaptar o restante processo para calcular o h-index.

A função |hindex| é representada pelo seguinte diagrama:

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Integer|^*
           \ar[d]_-{|ana qsep|}
           \ar[r]^-{| qsep |}
&
    |Either 1 (Integer, (Integer|^*|, Integer|^*|))|
           \ar[d]^{|id + id >< ((ana qsep) >< (ana qsep))|}
\\
    |BTree Integer|
           \ar[d]_-{|cataNat f|}
           \ar@@/_/[r]_-{|out|}
&
    |Either 1 (Integer,(BTree Integer,BTree Integer))|
           \ar[d]^{|id + id >< ((cata f) >< (cata f))|}
           \ar@@/_/[l]_-{|in|}
\\
    |(Integer, Integer|^*|)|
&
    |Either 1 (Integer, ((Integer, Integer|^*|), (Integer, Integer|^*|)))|
           \ar[l]^-{|f = either (const (0, [])) hI|}
}
\end{eqnarray*}

Esta função é composta por um anamorfismo (|anaBTree qsep|) e por um catamorfismo (|cataBTree (either (const (0, [])) hI)|).

\textbf{1. Anamorfismo}

A função |qsep| é responsável por dividir a lista de alturas do histograma e construir recursivamente a árvore binária.
Assim, caso a lista esteja vazia, retorna |i1()|.

Caso contrário, o primeiro elemento da lista é escolhido como pivô e os elementos restantes são divididos em dois subconjuntos: |s| contém os elementos menores que o pivô e |l| contém os elementos maiores ou iguais ao pivô.
Esta divisão é realizada pela função |part| que percorre a lista e verifica, para cada elemento, se este satisfaz o predicado |p|, no caso da função |qsep|, se é menor que o pivô.

Então, o resultado da função |qsep| é uma árvore binária onde cada nodo contém um pivô e as suas subárvores representam os valores menores e maiores, respetivamente.

\textbf{2. Catamorfismo}

O catamorfismo |cataBTree (either (const (0, [])) hI)| verifica se o nodo é vazio e retorna |(0, [])|.
Caso contrário, aplica a função |hI| que calcula o h-index e os contribuidores para o nodo atual.

A função |hI| segue os seguintes passos:

\textbf{2.1. Combinação dos valores das subárvores:} junta os valores das subárvores esquerda e direita numa lista, adicionando o valor do nodo atual.

\textbf{2.2. Cálculo do h-index:} cada elemento da lista é emparelhado com a sua posição usando |zip [1..] list|, a função |myfoldr| percorre esses pares para calcular o maior índice |k| tal que o valor associado seja maior ou igual a |k|.
Ou seja, a lista |list| é transformada em pares |(k, height)|, onde |k| representa a posição e |height| é o alor da altura correspondente. A função |process| verifica:
\begin{itemize}
    \item Se |height >= k|, então o h-index é atualizado para o máximo entre o valor atual e |k|.
    \item Caso contrário, o h-index mantém-se inalterado.
\end{itemize}
A função |process|:
\begin{itemize}
    \item verifica se a altura é maior ou igual ao índice: |uncurry (>=).swap.p1|;
    \item se a condição for satisfeita, atualiza o h-index: |uncurry max . swap . (p1 >< id)|;
    \item caso contrário, mantém o valor atual: |p2|.
\end{itemize}

\textbf{2.3. Identificação dos contribuidores:} a lista é filtrada para conter apenas os valores maiores ou iguais ao h-index (|filter (>= hIndex) list|).

Segue a implementação da função |hindex|:
\begin{code}
hindex = hyloBTree (either (const (0, [])) hI) qsep

hI :: (Int, ((Int, [Int]), (Int, [Int]))) -> (Int, [Int])
hI (n, ((_, ll), (_, lr))) = (hIndex, contributors)
    where
        list = lr ++ [n] ++ ll
        hIndex = myfoldr (curry process) 0 (zip [1..] list)
        process :: (Ord a) => ((a, a), a) -> a
        process = cond (uncurry (>=).swap.p1) (uncurry max . swap . (p1 >< id)) p2
        contributors = filter (>= hIndex) list
\end{code}

\subsection*{Problema 2}

Primeira parte:

A função |primes| é responsável por criar a lista de fatores primos de um dado número. De modo que, esta função pode ser definida
como um anamorfismo de listas (|List|). Assim, o diagrama que representa a operação é o seguinte:

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Integer|
           \ar[d]_-{|anaList g|}
            \ar[r]^-{|g|} 
&
    |1 + Integer| \times |Integer|
           \ar[d]^{|id + (id| \times |anaList g|)}
\\
     |Integer|^*
            \ar@@/_/[r]_-{|out|_|List|} 
&
     |1 + Integer| \times |Integer|^*
           \ar@@/_/[l]_-{|in|_|List|}
}
\end{eqnarray*}

A implementação baseia-se em decompor o número repetidamente no seu menor fator primo, este processo repete-se até que o quociente resultante seja 1.

O processo pode ser representado graficamente como se segue para o número 455:

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |455|
        \ar[d]
\\
    |(5,91)|
        \ar[d]
\\
    |(7,13)|
        \ar[d]
\\
    |(13,1)|
        \ar[d]
\\
    |[]|
}
\end{eqnarray*}

Assim, |primes 455 = [5,7,13]|.

A definição de |primes| como |anaList g| tira partido de que um anamorfismo constrói uma estrutura recursiva ao aplicar sucessivamente o gene |g| a um valor inicial.
O gene |g| determina como cada passo da construção ocorre, neste caso |g| divide o número |n| no seu menor fator primo (calculado pela função |smallestPrimeFactor|) e no quociente resultante após a divisão.
O processo termina quando |n=1|, porque não existem mais fatores primos para serem determinados.

A função |smallestPrimeFactor| é responsável por determinar o menor fator primo de um número |n|, e é definida como um catamorfismo de naturais (|catNat|).
Esta função aplica sucessivamente a lógica de "testar se um divisor |d| divide |n|" para valores |d| crescentes, assim inicia com o menor número primo (|2|).

O ciclo-for contém uma estrutura recursiva que verifica duas condições:

1. \textbf{Teste de primalidade:} Se \begin{math} d^2 > n\end{math}: Nesse caso, |n| é primo e o seu menor fator primo é ele mesmo (o processo termina).

2. \textbf{Encontrar o menor fator primo:} Se \begin{math}n\mod d = 0\end{math}: Nesse caso, |d| é o menor fator primo de |n|.

\textbf{Caso contrário:} Incrementámos |d| e continuámos o processo.
\paragraph{}
\textbf{Fundamentação matemática:}
A implementação baseia-se no Teorema Fundamental da Aritmética, que garante que todo o número inteiro positivo maior que 1
pode ser decomposto de forma única como um produto de fatores primos.
O processo descrito no gene |g| utiliza esta propriedade para decompor iterativamente o |n| nos seus fatores primos,
onde a divisibilidade é verificada e avançamos na procura do menor fator primo.

\begin{code}

smallestPrimeFactor x = for (\n -> cond (uncurry (>) . ((^2) >< id)) p2
                                     (cond ((== 0) . uncurry mod . swap) p1 (succ . p1)) (n,x)) 2 x

g 1 = i1 ()
g n = i2 (smallestPrimeFactor n, div n (smallestPrimeFactor n))

primes = anaList g
\end{code}

Segunda parte:

A função |prime_tree| é responsável por criar a árvore dos primos de uma lista de inteiros, como se encontra ilustrado no enunciado.
De modo que, esta função pode ser definida da seguinte forma:

\begin{code}
prime_tree = Term 1 . untar . map (\n -> (primes n, n))
\end{code}

Inicialmente, adotámos uma abordagem extensiva para resolver o problema, com a definição de um hilomorfismo e todas as operações necessárias para construir a árvore.
No entanto, durante este processo, reparámos na função |untar| da biblioteca |Exp.hs|, que efetua a operação necessária para transformar uma lista de pares numa estrutura do tipo |[Exp v o]|.
Após compreendermos o comportamento e a definição da função |untar|, percebemos que era possível utilizá-la na construção da função |prime_tree|, o que simplificou a implementação.

Explicação da função |prime_tree|:

1. A função |primes| é aplicada a cada elemento da lista de inteiros e com o uso da expressão |map (\n -> (primes n, n))|, obtemos uma lista de pares, onde o primeiro elemento é a lista de fatores primos de um número e o segundo elemento é o próprio número.
Assim, no final da execução desta expressão, obtemos uma lista de pares do tipo |[([Integer], Integer)]|.

2. Neste contexto, a função |untar| converte os fatores primos de um número e o próprio número numa representação de árvore onde os nodos intermediários são os fatores e as folhas são os números originais, |[Exp Integer Integer]|.
Esta conversão é realizada em três partes principais: a coalgebra, a base e a álgebra.

2.1. A coalgebra, representada pela função |c|, é responsável por decompor os dados, ou seja, separa os pares da lista inicial - |[([Integer], Integer)]| - e transforma cada elemento para o formato |Either Integer (Integer, [([Integer], Integer)])|.

2.1.1. O |map((p2 + assocr).distl.(outList >< id))| é aplicado a cada par da lista, onde:
    \begin{itemize}
        \item |outList >< id| transforma a lista de fatores primos num tipo |Either| e retorna o número original. Permitindo tratar em separado os fatores primos e os números. 
        \item |distl| distribui os elementos |Either (a, b)| para o tipo |(Either a b, b)|, separa os dados para facilitar o processamento posterior.
        \item |p2 + assocr| reorganiza os pares para agrupar corretamente os fatores primos associados a um número.
    \end{itemize}

2.1.2. |sep| percorre a lista de elementos |Either|, e separa os elementos |Left| para o primeiro grupo e os |Right| para o segundo grupo.

2.1.3. |id >< collect| aplica a função |id| ao primeiro valor do tuplo e |collect| ao segundo, de modo que a função |collect| é responsável por agrupar os fatores primos em listas separadas para cada número.
Então, os números que partilham o mesmo fator primo são agrupados juntos.

2.1.4. |join| junta os valores numa lista única, recriando a estrutura necessária para representare os dados.

2.2. Após a coalgebra, avançamos para a base, esta aplica recursivamente a função |untar| a cada sublista e cria subárvores para cada conjunto de fatores. O tipo da função |base| é definido como:

|base :: (Integer -> Integer) -> (Integer -> Integer) -> ([([Integer], Integer)] -> [Exp Integer Integer]) 
 -> [Either Integer (Integer, [([Integer], Integer)])] -> [Either Integer (Integer, [Exp Integer Integer])]|.

2.3. Para finalizar, a álgebra |a| organiza os dados processados na estrutura final, a operação |sort| organiza os nodos, enquanto que o |map inExp| converte os elementos numa estrutura do tipo |Exp Integer Integer|.
O seu tipo, neste contexto, é definido como: | a :: [Either Integer (Integer, [Exp Integer Integer])] -> [Exp Integer Integer]|.

3. Por fim, a função |Term 1| é aplicada para adicionar a raíz da árvore com o valor 1, isto conecta todas as subárvores criadas pela função |untar|, construindo uma única árvore que representa a decomposição de todos os números da lista.

\subsection*{Problema 3}

\begin{code}
convolve :: Num a => [a] -> [a] -> [a]
convolve l1 l2 = anaList (anaGene l1 l2) 0

anaGene :: Num a => [a] -> [a] -> Int -> Either () (a, Int)
anaGene l1 l2 = cond (>= m + n - 1) (const $ i1 ())
                    (\i -> i2 (sum  $ zipWith (*) l1 (map (\j -> access (l2, (i, j))) [0..(m - 1)]), i + 1))
    where
        m = length l1; n = length l2
        access = cond ((||) <$> cond1 <*> cond2) (const 0) (uncurry (!!) . (id >< uncurry (-)))
        cond1 = uncurry (>).(const 0 >< uncurry (-))
        cond2 = uncurry (<=).(length >< uncurry (-))

\end{code}

\subsection*{Problema 4}

1. Nesta pergunta, pretende-se definir por completo, a biblioteca |Expr|, à semelhança das outras bibliotecas de estruturas fornecidas.

Definição do tipo de |Expr|:

Para o cálulo de |outExpr|, partimos da afirmação |outExpr . inExpr = id|,

\begin{eqnarray*}
\start
|
     outExpr . inExpr = id
|
\just\equiv{def inExpr}
|
     outExpr . either V (either N (uncurry T)) = id
|
\just\equiv{ fusão + }
|
     either (outExpr . V) (either (outExpr . N) (outExpr . uncurry T)) = id
|
\just\equiv{ universal +, natural id }
|
    lcbr(
          outExpr . V = i1
     )(
          either (outExpr . N) (outExpr . uncurry T) = i2
     )
|
\just\equiv{ universal + }
|
    lcbr3(
          outExpr . V = i1
     )(
          outExpr . N = i2 . i1
     )(
          outExpr . uncurry T = i2 . i2
     )
|
\just\equiv{ igualdade extensional, def-comp, uncurry }
|
    lcbr3(
          outExpr (V n) = i1 n
     )(
          outExpr (N n) = (i2 . i1) n
     )(
          outExpr (T op exprs) = (i2 . i2) (op, exprs)
     )
|
\end{eqnarray*}

Ficando assim, em Haskell, com:

\begin{code}

outExpr :: Expr b a -> Either a (Either b (Op, [Expr b a]))
outExpr (V n) = i1 n
outExpr (N n) = (i2.i1) n
outExpr (T op exprs) = (i2.i2) (op,exprs)

\end{code}

Cálculo do functor de |Expr|:

Sabendo que |F f = B(id, f)|, temos que:

\begin{eqnarray*}
\start
|
    F f = B(id, id, f)
|
\just\equiv{ def B }
|
    F f = id + (id + id >< map f)
|
\end{eqnarray*}

Definindo, então, |recExpr| como:

\begin{code}

recExpr :: (a -> b1) -> Either b2 (Either b3 (b4, [a])) -> Either b2 (Either b3 (b4, [b1]))
recExpr = baseExpr id id

\end{code}

Definição da triologia ana-cata-hylo:

Começando pelo catamorfismo de |Expr|, temos:

\begin{eqnarray*}
\start
\just\equiv{ cancelamento-cata }
|
    cata g . inT = g . fF (cata g)
|
\just\equiv{ shunt-left }
|
    cata g = g . fF (cata g) . outT
|
\end{eqnarray*}

Representado pelo seguinte diagrama:

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Expr C A|
           \ar[d]_-{|cataNat g|}
           \ar@@/^-1pc/[r]_-{| out |}
&
    |A + (C + (Op >< (Expr C A)|^*))
           \ar[d]^{|id + (id + (id >< map (cataNat g)))|}
           \ar@@/^-1pc/[l]_-{|inNat |}
\\
    |Expr C B|
&
    |A + (C + (Op >< (Expr C B)|^*))
           \ar[l]^-{|g|}
}
\end{eqnarray*}

Utilizando as funções previamente definidas, temos então:

\begin{code}

cataExpr g = g . recExpr (cataExpr g) . outExpr

\end{code}

Para o anamorfismo de |Expr|, temos:

\begin{eqnarray*}
\start
\just\equiv{ cancelamento-ana }
|
    outT . ana g = fF (ana g) . g
|
\just\equiv{ shunt-right }
|
    ana g = inT . fF (ana g) . g
|
\end{eqnarray*}

Representado pelo seguinte diagrama:

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Expr C A|
           \ar@@/^-1pc/[r]_-{| out |}
&
    |A + (C + (Op >< (Expr C A)|^*))
           \ar@@/^-1pc/[l]_-{|inNat |}
\\
    |Expr C D|
            \ar[u]^-{|ana g|}
            \ar[r]_-{|g|}
&
    |A + (C + (Op >< (Expr C D)|^*))
            \ar[u]_-{|id + (id + (id >< map (ana g)))|}
}
\end{eqnarray*}

Utilizando as funções previamente definidas, temos então:

\begin{code}

anaExpr g = inExpr . recExpr (anaExpr g) . g

\end{code}

Sendo o hilomorfismo, a composição do catamorfismo e do anamorfismo, representado pelo seguinte diagrama:

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Expr C D|
           \ar[d]_-{|ana g|}
           \ar[r]_-{| g |}
&
    |A + (C + (Op >< (Expr C D)|^*))
           \ar[d]^{|id + (id + (id >< map (ana g)))|}
\\
    |Expr C A|
           \ar[d]_-{|cataNat h|}
           \ar@@/^-1pc/[r]_-{| out |}
&
    |A + (C + (Op >< (Expr C A)|^*))
           \ar[d]^{|id + (id + (id >< map (cataNat h)))|}
           \ar@@/^-1pc/[l]_-{|inNat |}
\\
    |Expr C B|
&
    |A + (C + (Op >< (Expr C B)|^*))
           \ar[l]^-{|h|}
}
\end{eqnarray*}

ou seja,

\begin{eqnarray*}
\start
|
    hylo h g = cata h . ana g
|
\end{eqnarray*}

Este é definido em Haskell usando as funções |cataExpr| e |anaExpr| previamente definidas:

\begin{code}
                
hyloExpr h g = cataExpr h . anaExpr g

\end{code}

\emph{Monad}:

Para declarar |Expr b| como instância da classe |Monad|, foram implementadas as intâncias de |Functor|, |Applicative| e |Monad| do tipo |Expr b|.
A abordagem utilizada foi guiada pelo exercício 4 da ficha 12, adaptando ao contexto específico de |Expr b|.

Começamos pelo |Functor|, onde a função |fmap| aplica uma transformação às variáveis da expressão, mantendo as restantes estruturas (|N| e |T|) inalteradas.
Esta operação é realizada de forma recursiva usando o catamorfismo - |cataExpr| -, que reconstrói a expressão após aplicar a |f| às variáveis.
A composição com a função |inExpr| e a base do catamorfismo (|baseExpr|) assegura que a estrutura é processada corretamente.

\begin{code}

instance Functor (Expr b)
     where fmap f = cataExpr (inExpr . baseExpr f id id)

\end{code}

De seguida, definimos a instância |Applicative|, onde a função |pure| cria uma expressão com uma variável (|V|) com o valor fornecido,
a função |<*>| considera três casos:
\begin{itemize}
\item se a expressão é uma variável (|V f|), aplica |fmap| para mapear função sobre a outra expressão;
\item se a expressão é um número (|N b|), mantém o número inalterado;
\item se a expressão é uma operação (|T op fs|), aplica a função a cada subexpressão da operação.
\end{itemize}

\begin{code}

instance Applicative (Expr b) where
    pure :: a -> Expr b a
    pure = V
    (V f) <*> x = fmap f x
    (N b) <*> _ = N b
    (T op fs) <*> x = T op (map (<*> x) fs)

\end{code}

Por fim, a instância |Monad| foi definida, a definição |return| é equivalente a |pure|, cria uma variável.
A operação |>>=| aplica a função |g| a cada variável da expressão, usando a função auxiliar |muExpr| para processar a expressão resultante.

\begin{code}

instance Monad (Expr b) where
    return :: a -> Expr b a
    return = pure

    (>>=) :: Expr b a -> (a -> Expr b b1) -> Expr b b1
    t >>= g = muExpr (fmap g t)

muExpr :: Expr b (Expr b a) -> Expr b a
muExpr  =  cataExpr (either id (inExpr . i2))

u :: a -> Expr b a
u = V

\end{code}

Provemos que |Expr b| é uma instância de |Monad|:
\begin{itemize}
\item |u = V| e |V = inExpr . i1|, logo |u = inExpr . i1|;
\item |muExpr = cataExpr (either id (inExpr . i2))|.
\end{itemize}

Provar a lei monádica Unidade (63):
\begin{eqnarray*}
\start
|
	mu . u = mu . T u
|
\just\equiv{ definição de mu; definição de u }
|
    cata (either id (in . i2)) . in . i1 = cata (either id (in . i2)) . T u
|
\just\equiv{ absorção-cata }
|
    cata (either id (in . i2)) . in . i1 = cata (either id (in . i2) . B(u,id))
|
\just\equiv{ B(f,g) = f + G g, absorção-+, natural-id, functor-id-F }
|
    cata (either id (in . i2)) . in . i1 = cata (either u (in.i2))
|
\just\equiv{ definição de u, cancelamento-cata }
|
    either id (in . i2) . F mu . i1 = cata (either (in.i1) (in.i2))
|
\just\equiv{ fusão-+, reflexão-+, reflexão-cata, base-cata, B(id, mu) = id + G mu }
|
    either id (in . i2) . (id + G mu) . i1 = id
|
\just\equiv{ natural-i1, natural-id }
|
    either id (in . i2) . i1 = id
|
\just\equiv{ cancelamento-+ }
|
    id = id
|
\just\equiv{ P.R.I. }
|
    True
|
\qed
\end{eqnarray*}

Provar a lei monádica Multiplicação (62):
\begin{eqnarray*}
\start
|
	mu . mu = mu . T mu
|
\just\equiv{ definição de mu }
|
    mu.mu = cata (either id (in . i2)) . T cata (either id (in . i2))
|
\just\equiv{ absorção-cata }
|
    mu.mu = cata (either id (in . i2) . (cata (either id (in.i2)) + G id))
|
\just\equiv{ Functor-id-F, natural-id, absorção-+ }
|
    mu.mu = cata (either (cata (either id (in.i2))) (in.i2))
|
\just\equiv{ definição de mu }
|
    mu.cata (either id (in.i2)) = cata (either (cata (either id (in.i2))) (in.i2))
|
\just\Leftarrow{ fusão-cata }
|
    mu. either id (in.i2) = either (cata (either id (in.i2))) (in.i2) . (id + G mu)
|
\just\equiv{ fusão-+, absorção-+, natural-id, eq-+ }
|
    either id (in . i2) . i1 = id
|
\just\equiv{ cancelamento-+ }
|
    lcbr(
          mu = mu
     )(
          mu . in . i2 = in . i2 . G mu
     )
|
\just\equiv{ p \& True = True, definição de mu, cancelamento-cata, base-cata }
|
    either id (in . i2) . (id + G mu) . i2 = in . i2 . G mu
|
\just\equiv{ natural-i2, cancelamento-+ }
|
    in . i2 . G mu = in . i2 . G mu
|
\just\equiv{ P.R.I }
|
    True
|
\qed
\end{eqnarray*}

\emph{Maps}:
\emph{Monad}:
\emph{Let expressions}:

A função |let_exp| é responsável por substituir todas as variáveis numa expressão |Expr| pelas suas correspondentes expressões
atribuídas por uma função fornecida como argumento.

A definição da função |let_exp| utiliza o catamorfismo |cataExpr|. No caso de encontrar uma variável (|V|), 
a função |f| é usada para substituir essa variável pela expressão correspondente. Para valores 
numéricos (|N|), a função mantém o valor inalterado. Para operadores (caso |T|), a função constrói uma nova expressão 
que combina os resultados das subexpressões recursivamente.

Em suma, |let_exp| avalia uma expressão ao substituir todas as variáveis pelas expressões correspondentes, garantindo 
que a estrutura da expressão original é mantida. De seguida, o diagrama mostra como a operação do catamorfismo percorre e 
transforma a expressão.

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Expr C A|
           \ar[d]_-{|let_exp f|}
           \ar@@/_/[r]_-{|out|_|Expr|}
&
    |A + (C + (Op >< (Expr C A)|^*))
           \ar[d]^{|id + (id + (id >< map (let_exp f)))|}
           \ar@@/_/[l]_-{|in|_|Expr|}
\\
    |Expr C B|
&
    |A + (C + (Op >< (Expr C B)|^*))
           \ar[l]^-{|either f (either N (uncurry T))|}
}
\end{eqnarray*}

Segue a implementação da função |let_exp|:

\begin{code}
let_exp f = cataExpr (either f (either N (uncurry T)))
\end{code}

Catamorfismo monádico:
\begin{code}
mcataExpr g = g .! (dl' . recExpr (mcataExpr g) . outExpr)

dl' :: Monad m => Either a (Either b (Op, [m c])) -> m (Either a (Either b (Op, m [c])))
dl' = either (return . i1) (either (return . i2 . i1) aux)
    where aux (op, ms) = do m <- lamb ms; (return . i2 . i2) (op, return m)
\end{code}


Avaliação de expressões:

A função |evaluate| avalia expressões do tipo |Expr| e retorna o resultado da avaliação com o tipo |Maybe|.
Esta função tem em conta dois cenários de erro: variáveis não instanciadas e operadores aplicados a um número incorreto de argumentos.

A função |evaluate| utiliza o catamorfismo |mcataExpr| para avaliar a expressão. Este conceito generaliza o conceito de catamorfismo simples para permitir trabalhar em contextos monádicos.
O ponto central deste conceito é que combina a lógica de transformação (|g|) com a recursão da estrutura, enquanto lida automaticamente com contextos monádicos. Assim, evitámos
tratar manualmente de cada contexto monádico |Maybe| em cada passo.

No caso do |evaluate|, o gene |gene| define como é que se processa cada nodo da estrutura |Expr|.
O gene |gene| lida com três casos principais:
\begin{itemize}
\item |V| : Para uma variável, retornámos |Nothing|, porque as variávis não podem ser avaliadas.
\item |N| : Para um número, retornámos o próprio número com |Just|.
\item |T| : Para um operador, utilizámos a função auxiliar |aux| que:
    \begin{itemize}
        \item avalia todos os argumentos no contexto |Maybe|, isto é, verifica se todos os argumentos são válidos;
        \item aplica a função |result| para calcular o resultado final, caso todos os argumentos sejam válidos.
    \end{itemize}
\end{itemize}

A função |result| define o comportamento esperado para cada operados e valida a aridade, assim garante que apenas os operadores com a aridade correta sejam avaliados.
Caso contrário, a avaliação falha e retorna |Nothing|.

Segue a implementação da função |evaluate|:

\begin{code}
evaluate = mcataExpr gene

gene :: (Num a, Ord a) => Either b (Either a (Op, Maybe [a])) -> Maybe a
gene = either (const Nothing) (either Just aux)
    where aux (op, args) = do argsR <- args; result op argsR

result :: (Num a, Ord a) => Op -> [a] -> Maybe a
result Add [x, y] = Just (x + y)
result Mul [x, y] = Just (x * y)
result Suc [x] = Just (x + 1)
result ITE [cond, t, f] = if cond /= 0 then Just t else Just f
result _ _ = Nothing

\end{code}

%----------------- Índice remissivo (exige makeindex) -------------------------%

\printindex

%----------------- Bibliografia (exige bibtex) --------------------------------%

\bibliographystyle{plain}
\bibliography{cp2425t}

%----------------- Fim do documento -------------------------------------------%
\end{document}
