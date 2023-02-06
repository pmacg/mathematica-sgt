(* ::Package:: *)

(* ::Title:: *)
(*Spectral Graph Theory*)


(* ::Text:: *)
(*This package includes various functions for studying spectral graph theory with Mathematica.*)


(* ::Subsection::Closed:: *)
(*Boilerplate*)


(* ::Text:: *)
(*This section is just the code needed to create the package.*)


(* ::Input:: *)
(*BeginPackage["SGT`"]*)
(*Unprotect@@Names["SGT`*"];*)
(*ClearAll@@Names["SGT`*"];*)


(* ::Subsection:: *)
(*Documentation for public methods*)


(* ::Input:: *)
(*combineGraphs::usage="combineGraphs[g1,g2,conections]";*)
(*spectrumAdjacency::usage="spectrumAdjacency[g]";*)
(*laplacian::usage="laplacian[g]";*)
(*spectrumLaplacian::usage="spectrumLaplacian[g]";*)
(*laplacianNormalised::usage="laplacianNormalised[g]";*)
(*spectrumLaplacianNormalised::usage="spectrumLaplacianNormalised[g]";*)
(*effectiveResistances::usage="effectiveResistances[lapMat]";*)


(* ::Subsection::Closed:: *)
(*Boilerplate*)


(* ::Input:: *)
(*Begin["`Private`"]*)


(* ::Subsection:: *)
(*Graph Construction*)


(* ::Text:: *)
(*Utilities for helping with constructing Graph objects.*)


renumberedEdges[g_,min_]:=
	(#/.UndirectedEdge[a_,b_]->UndirectedEdge[a+min,b+min])&/@
	((#/.DirectedEdge[a_,b_]->DirectedEdge[a+min,b+min])&/@
	EdgeList[g])


renumberGraph[g_,min_]:=Graph[
	renumberedEdges[g,min]
]


combineGraphs[g1_,g2_,connections_]:=GraphUnion[
g1,
renumberGraph[g2,Max[VertexList[g1]]],
Graph[
	(#/.UndirectedEdge[a_,b_]->UndirectedEdge[a,b+Max[VertexList[g1]]])&/@
	((#/.DirectedEdge[a_,b_]->DirectedEdge[a,b+Max[VertexList[g1]]])&/@
	connections)]
]


combineGraphs[g1_,g2_]:=combineGraphs[g1,g2,{}]


reverseDirectedGraph[g_]:=Graph[VertexList[g],(#[[2]]->#[[1]])&/@EdgeList[g]]


(* ::Text:: *)
(*Given two graphs, connect them with a random cut. G1 must have less than or equal the number of vertices in G2.*)


randomlyConnect[G1_,G2_,p_]:=With[{
	A1=AdjacencyMatrix[G1],
	A2=AdjacencyMatrix[G2],
	n1=VertexCount[G1],
	n2=VertexCount[G2]},
	With[{
		C=AdjacencyMatrix[UndirectedGraph[imbalancedDsbm[n1,n2,0,p,1]]]},
	Join[
		(Join[A1[[#]],C[[#,n1+1;;n1+n2]]])&/@Range[n1],
		(Join[C[[#,1;;n1]],A2[[#-n1]]])&/@Range[n1+1,n1+n2]
	]
	]
]//SparseArray//AdjacencyGraph


randomlyConnectDirected[G1_,G2_,p_,f_]:=With[{
A1=AdjacencyMatrix[G1],
A2=AdjacencyMatrix[G2],
n1=VertexCount[G1],
n2=VertexCount[G2]},
With[{
C=AdjacencyMatrix[imbalancedDsbm[n1,n2,0,p,f]]},
Join[
(Join[A1[[#]],C[[#,n1+1;;n1+n2]]])&/@Range[n1],
(Join[C[[#,1;;n1]],A2[[#-n1]]])&/@Range[n1+1,n1+n2]
]
]
]//SparseArray//AdjacencyGraph





(* ::Text:: *)
(*Create an easy constructor for an Erdos-Renyi graph.*)


erdosGraph[n_,p_]:=RandomGraph[BernoulliGraphDistribution[n,p]]


(* ::Text:: *)
(*Below is a convenient constructor of a 'barbell' graph - two complete graphs joined by an edge.*)


barbellGraph[n_]:=GraphUnion[combineGraphs[CompleteGraph[n],CompleteGraph[n]],Graph[{n<->n+1}]]


barbellPathGraph[n_,m_]:=combineGraphs[combineGraphs[CompleteGraph[n],PathGraph[Range[m-1]],{n\[UndirectedEdge]1}],CompleteGraph[n],{n+m-1\[UndirectedEdge]1}]


incompleteBarbell[n_,p_]:=GraphUnion[combineGraphs[erdosGraph[n,p],erdosGraph[n,p]],Graph[{n<->n+1,n-1<->n+2}]]


threeBarbell[n_]:=GraphUnion[combineGraphs[barbellGraph[n],CompleteGraph[n]],Graph[{2n<->2n+1}]]


imbalancedBarbell[n1_,n2_]:=GraphUnion[combineGraphs[CompleteGraph[n1],CompleteGraph[n2]],Graph[{n1<->n1+1}]]


imbalancedThreeBarbell[n1_,n2_,n3_]:=GraphUnion[combineGraphs[imbalancedBarbell[n1,n2],CompleteGraph[n3]],Graph[{(n1+n2)<->(n1+n2)+1}]]


(* ::Text:: *)
(*Construct an 'almost bipartite' graph.*)


almostBipartite[n_,p_,q_]:=GraphUnion[combineGraphs[erdosGraph[n,p],erdosGraph[n,p]],GraphDifference[CompleteGraph[{n,n}],erdosGraph[2n,1-q]]]


almostBipartite[n_,p_]:=GraphUnion[combineGraphs[erdosGraph[n,1-p],erdosGraph[n,1-p]],GraphDifference[CompleteGraph[{n,n}],erdosGraph[2n,1-p]]]


(* ::Text:: *)
(*Remove the self-loops from a given graph.*)


removeSelfLoops[G_]:=AdjacencyGraph[AdjacencyMatrix[G]-DiagonalMatrix[Diagonal[AdjacencyMatrix[G]]]]


(* ::Subsection:: *)
(*Stochastic Block Models*)


(* ::Text:: *)
(*This section gives some additional graph constructions  based on several stochastic block models.*)


(* ::Text:: *)
(*The first is the directed SBM defined by Cucuringu, Li, Sun, and Zanetti '19. The function below returns a graph drawn from the model with the given parameters.*)


dsbm[n_,p_,q_,F_]:=Graph[
	Range[0,(n*Length[F])-1],
	Flatten[Union[
		Flatten[RandomChoice[{p/2,p/2,1-p}->{#[[1]]->#[[2]],#[[2]]->#[[1]],{}}]&/@
			Flatten[Function[offset,Subsets[Range[n*(offset-1),(n*offset)-1],{2}]]/@Range[Length[F]],1]
		],
		Function[ks,
			Flatten[RandomChoice[{q*(F[[ks[[1]],ks[[2]]]]),q*(F[[ks[[2]],ks[[1]]]]),1-q}->{#[[1]]->#[[2]],#[[2]]->#[[1]],{}}]&/@
				Flatten[Outer[List,Range[n*(ks[[1]]-1),(n*ks[[1]])-1],Range[n*(ks[[2]]-1),(n*ks[[2]])-1]],1]
			]
		]/@Subsets[Range[Length[F]],{2}]
	]]
]


generalDSBM[ns_,ps_,Q_,F_]:=Graph[
Range[0,Total[ns]-1],
Flatten[Union[
		Flatten[Function[offset,
			RandomChoice[{ps[[offset]]/2,ps[[offset]]/2,1-ps[[offset]]}->{#[[1]]->#[[2]],#[[2]]->#[[1]],{}}]&/@
				Subsets[Range[Sum[ns[[i]],{i,1,offset-1}],Sum[ns[[i]],{i,1,offset}]-1],{2}]]/@Range[Length[F]],1],
		Function[ks,
			Flatten[RandomChoice[{Q[[ks[[1]],ks[[2]]]]*(F[[ks[[1]],ks[[2]]]]),Q[[ks[[2]],ks[[1]]]]*(F[[ks[[2]],ks[[1]]]]),1-Q[[ks[[1]],ks[[2]]]]}->{#[[1]]->#[[2]],#[[2]]->#[[1]],{}}]&/@
				Flatten[Outer[List,Range[Sum[ns[[i]],{i,1,(ks[[1]]-1)}],Sum[ns[[i]],{i,1,ks[[1]]}]-1],Range[Sum[ns[[i]],{i,1,ks[[2]]-1}],Sum[ns[[i]],{i,1,ks[[2]]}]-1]],1]
			]
		]/@Subsets[Range[Length[F]],{2}]
	]]
]


(* ::Text:: *)
(*Create a helper function just for constructing the classic ' triangle' example for the dsbm.*)


triangleDSBM[n_,internalEdgeProb_,externalEdgeProb_,flowProb_]:=dsbm[n,internalEdgeProb,externalEdgeProb,{{1/2,flowProb,1-flowProb},{1-flowProb,1/2,flowProb},{flowProb,1-flowProb,1/2}}]


(* ::Text:: *)
(*Allow returning the ground truth clustering along with the graph.*)


dsbmWithGT[n_,p_,q_,F_]:={dsbm[n,p,q,F],Partition[Range[0,(n*Length[F])-1],n]}


(* ::Text:: *)
(*Imbalanced dsbm with two clusters of sizes Subscript[n, 1] and Subscript[n, 2]. n1 needs to be smaller than n2.*)


imbalancedDsbm[n1_,n2_,p_,q_,f_]:=Subgraph[dsbm[n2,p,q,{{1/2,f},{1-f,1/2}}],Range[n2-n1,2*n2]]


imbalancedDsbm[n1_,n2_]:=imbalancedDsbm[n1,n2,1,1,1]


(* ::Text:: *)
(*Simple two cluster dsbm.*)


simpleDsbm[n_,p_,q_,f_]:=imbalancedDsbm[n,n,p,q,f]


simpleDsbm[n_]:=simpleDsbm[n,1,1,1]


(* ::Text:: *)
(*A completely general SBM model for undirected graphs.*)


edgesForCluster[c1_,c2_,prob_]:=With[
{numEdges=RandomVariate[BinomialDistribution[Length[c1]*Length[c2],prob]]},
MapThread[UndirectedEdge,{RandomChoice[c1,numEdges],RandomChoice[c2,numEdges]}]
]


generalSBM[ns_,M_]:=Graph[Range[Total[ns]],
Flatten[Table[
	edgesForCluster[
		Range[Total[ns[[1;;i-1]]]+1,Total[ns[[1;;i-1]]]+ns[[i]]],
		Range[Total[ns[[1;;j-1]]]+1,Total[ns[[1;;j-1]]]+ns[[j]]],
		If[i==j,0.5M[[i,j]],M[[i,j]]]
	],
	{i,1,Length[M]},{j,i,Length[M]}
]]]


sbm[n_,k_,p_,q_]:=removeSelfLoops[generalSBM[Table[n,{i,1,k}],Table[If[i==j,p,q],{i,1,k},{j,1,k}]]]


(* ::Text:: *)
(*And the same SBM for directed graphs.*)


dsbm[ns_,M_]:=Graph[Range[Total[ns]],
Flatten[Table[
	(#[[1]]\[DirectedEdge]#[[2]])&/@ edgesForCluster[
		Range[Total[ns[[1;;i-1]]]+1,Total[ns[[1;;i-1]]]+ns[[i]]],
		Range[Total[ns[[1;;j-1]]]+1,Total[ns[[1;;j-1]]]+ns[[j]]],
		If[i==j,M[[i,j]],M[[i,j]]]
	],
	{i,1,Length[M]},{j,1,Length[M]}
]]]


(* ::Text:: *)
(*Get the list of clusters for an SBM.*)


sbmClusters[k_,n_]:=(Range[(#-1)*n + 1,(#*n)])&/@Range[k]


(* ::Subsection:: *)
(*Hermitian Matrices for Directed Graphs*)


(* ::Text:: *)
(*This section gives some helper functions for  manipulating the Hermitian adjacency matrices that we use to study directed graphs.*)


hermitianAdjacency[G_]:=(AdjacencyMatrix[G]-Transpose[AdjacencyMatrix[G]])I


plotComplexEig[M_,n_]:=ListPlot[ReIm/@Eigenvectors[N[M],n][[n]],PlotRange->Full]


plotFirstComplexEig[G_]:=plotComplexEig[hermitianAdjacency[G],1]


plotSecondComplexEig[G_]:=plotComplexEig[hermitianAdjacency[G],2]


(* ::Text:: *)
(*Get the asymmetric, real transition matrix for a simple random walk on a directed graph.*)


outDegreeMatrix[G_]:=DiagonalMatrix[Total[Transpose[AdjacencyMatrix[G]]]]


inDegreeMatrix[G_]:=DiagonalMatrix[Total[AdjacencyMatrix[G]]]


fullDegreeMatrix[G_]:=outDegreeMatrix[G]+inDegreeMatrix[G]


directedRandomWalkMatrix[G_]:=Inverse[outDegreeMatrix[G]].AdjacencyMatrix[G]


symDegNormHermAdj[G_]:=Inverse[Sqrt[fullDegreeMatrix[G]]].hermitianAdjacency[G].Inverse[Sqrt[fullDegreeMatrix[G]]]


degNormHermAdj[G_]:=Inverse[fullDegreeMatrix[G]].hermitianAdjacency[G]


(* ::Text:: *)
(*The following is the directed clustering algorithm given by Cucuringu, Li, Sun, Zanetti 2019.*)


clszClusterDirectedGraph[G_,k_]:=FindClusters[
	Fold[Plus,(Outer[Times,#,#])&/@
		Eigenvectors[N[hermitianAdjacency[G]],2*Floor[k/2]]]
			->VertexList[G],
	k,
	Method->"KMeans"
]


(* ::Text:: *)
(*Define the Cut Imbalance ratio for a given subset of the vertices in a graph.*)


directedVolume[S_,G_]:=Total[VertexDegree[G,#]&/@S]


directedWeight[X_,Y_,G_]:=Length[Select[EdgeList[G],(MemberQ[X,#[[1]]]&& MemberQ[Y,#[[2]]])&]]


clszCutImbalance[X_,Y_,G_]:=Abs[directedWeight[X,Y,G]/(directedWeight[X,Y,G]+directedWeight[Y,X,G])-1/2]


(* ::Text:: *)
(*Add the two normalized versions of the cut imbalance.*)


clszCutImbalanceSize[X_,Y_,G_]:=clszCutImbalance[X,Y,G]*Min[{Length[X],Length[Y]}]


clszCutImbalanceVolume[X_,Y_,G_]:=clszCutImbalance[X,Y,G]*Min[{directedVolume[X,G],directedVolume[Y,G]}]


(* ::Text:: *)
(*Calculate a random walk for some number of steps.*)


calcRandWalk[W_,x0_,n_]:=Nest[(#.W)&,x0,n]


(* ::Subsection:: *)
(*Graph Spectrum*)


(* ::Text:: *)
(*This section includes methods used for calculating the spectrum of a graph.*)


getEigenvalues[m_,n_]:=Chop[Sort[Eigenvalues[SetPrecision[m,MachinePrecision],n],(#1<#2)&]]//N


getEigenvalues[m_]:=Chop[Sort[Eigenvalues[SetPrecision[m,MachinePrecision]],(#1<#2)&]]//N


spectrumAdjacency[g_,n_]:=getEigenvalues[AdjacencyMatrix[g],n]


spectrumAdjacency[g_]:=getEigenvalues[AdjacencyMatrix[g]]


laplacian[g_]:=DiagonalMatrix[SparseArray[VertexDegree[g]]]-AdjacencyMatrix[g]


spectrumLaplacian[g_,n_]:=getEigenvalues[laplacian[g],n]


spectrumLaplacian[g_]:=getEigenvalues[laplacian[g]]


laplacianNormalised[g_]:=IdentityMatrix[VertexCount[g],SparseArray]-(DiagonalMatrix[SparseArray[(1/Sqrt[#])&/@VertexDegree[g]]].AdjacencyMatrix[g].DiagonalMatrix[SparseArray[(1/Sqrt[#])&/@VertexDegree[g]]])


adjacencyNormalised[g_]:=(DiagonalMatrix[SparseArray[(1/Sqrt[#])&/@VertexDegree[g]]].AdjacencyMatrix[g].DiagonalMatrix[SparseArray[(1/Sqrt[#])&/@VertexDegree[g]]])


randomWalkLaplacian[g_]:=IdentityMatrix[VertexCount[g],SparseArray]-(DiagonalMatrix[SparseArray[(If[#!=0,1/#,#])&/@VertexDegree[g]]].AdjacencyMatrix[g])


spectrumLaplacianNormalised[g_,n_]:=getEigenvalues[laplacianNormalised[g],n]


spectrumLaplacianNormalised[g_]:=getEigenvalues[laplacianNormalised[g]]


(* ::Text:: *)
(*\[Lambda] (G) = Max( |Subscript[\[Lambda], 2]| , |Subscript[\[Lambda], n]| )*)


lambdaGraph[g_]:=Abs[spectrumAdjacency[g,2][[1]]]


(* ::Text:: *)
(*Get the Laplacian from the adjacency matrix.*)


degreeMatrix[G_]:=DiagonalMatrix[SparseArray[VertexDegree[G]]]


degreeFromAdjacency[A_]:=DiagonalMatrix[Total[Abs[Transpose[A]]]]


degreeMatrix[G_]:=degreeFromAdjacency[WeightedAdjacencyMatrix[G]]


laplacianFromAdjacency[A_]:=degreeFromAdjacency[A]-A


laplacianNormalisedFromAdjacency[A_]:=IdentityMatrix[Dimensions[A][[1]]]-Inverse[Sqrt[degreeFromAdjacency[A]]].A.Inverse[Sqrt[degreeFromAdjacency[A]]]


(* ::Text:: *)
(*Plot the first two eigenvectors*)


plotGraphEigs[G_]:=With[{eig1=Eigenvectors[laplacian[G]//N,-2][[-2]],
eig2=Eigenvectors[laplacian[G]//N,-3][[-3]]},
ListPlot[({eig1[[#]],eig2[[#]]})&/@Range[Length[eig1]],PlotRange->Full]
]


plotNormalisedGraphEigs[G_]:=With[{eig1=Eigenvectors[laplacianNormalised[G]//N,-2][[-2]],
eig2=Eigenvectors[laplacianNormalised[G]//N,-3][[-3]]},
ListPlot[({eig1[[#]],eig2[[#]]})&/@Range[Length[eig1]],PlotRange->Full]
]


clusterPoints[eigs_,cluster_]:=(eigs[[#]])&/@cluster


plotGraphEigsWithClusters[G_,e1_,e2_,clusters_]:=With[{eig1=Eigenvectors[laplacian[G]//N,-e1][[-e1]],
eig2=Eigenvectors[laplacian[G]//N,-e2][[-e2]]},
ListPlot[clusterPoints[Transpose[{eig1,eig2}],#]&/@clusters,PlotRange->Full]
]


plotGraphEigsWithClusters[G_,e1_,e2_,e3_,clusters_]:=With[{eig1=Eigenvectors[laplacian[G]//N,-e1][[-e1]],
eig2=Eigenvectors[laplacian[G]//N,-e2][[-e2]],
eig3=Eigenvectors[laplacian[G]//N,-e3][[-e3]]},
ListPointPlot3D[clusterPoints[Transpose[{eig1,eig2, eig3}],#]&/@clusters,PlotRange->Full]
]


(* ::Subsection:: *)
(*Sweep Set Algorithm*)


(* ::Text:: *)
(*This section gives an implementation of a general sweep set algorithm. orderedElements is the list of things you'd like to sweep over, in the order you'd like to sweep. The given function is the function which should be *maximized* during the sweep.*)


generalSweepSet[orderedElements_,function_]:=Take[
	orderedElements,
	Ordering[function/@(
		Take[orderedElements,#]&/@Range[Length[orderedElements]]
	),-1][[1]]
]


(* ::Text:: *)
(*Now we give an application of the general sweep set algorithm by finding a set of vertices in a graph which have a large Cut Imbalance as defined by Cucuringu, Li, Sun and Zanetti 2019.*)


flowSweepSet[orderedVertices_,G_]:=generalSweepSet[
	orderedVertices,
	clszCutImbalanceVolume[#,Complement[VertexList[G],#],G]&
]


(* ::Subsection:: *)
(*General Linear Algebra*)


(* ::Text:: *)
(*Check whether a vector is an eigenvector of a matrix. Truncates numbers to 10 decimal places - this is a numerical process so be careful about errors!*)


eigenvectorQ[matrix_, vector_] := MatrixRank[SetPrecision[{matrix . vector, vector},10]] == 1


(* ::Text:: *)
(*Get the eigenvalue for a given eigenvector.*)


eigenvalueOf[matrix_,vector_]:=If[eigenvectorQ[matrix,vector],(matrix.vector)[[1]]/vector[[1]],Undefined]


(* ::Text:: *)
(*The following is a simple implementation of the power method for computing the top eigenvalue and eigenvector of a matrix.*)


powerMethod[B_,x_,n_]:=Nest[(Normalize[B.#])&,x,n]


(* ::Text:: *)
(*The following method visualizes the distribution of values in a real eigenvector.*)


plotRealEig[M_,n_,b_ :20]:=Histogram[Eigenvectors[M,n][[n]],b,PlotRange->Full]


(* ::Text:: *)
(*A helper function for extracting the n^th eigenvector or eigenvalue of a matrix.*)


eigenvectorN[M_,n_]:=Eigenvectors[M//N,n][[n]]


eigenvalueN[M_,n_]:=Eigenvalues[M//N,n][[n]]


(* ::Text:: *)
(*Compute the Rayleigh quotient of a matrix with a vector.*)


rq[M_,v_]:=(Conjugate[v].M.v)/Conjugate[v].v


(* ::Text:: *)
(*Get only the positive part of a matrix.*)


pos[M_]:=Clip[M,{0,\[Infinity]}]


(* ::Text:: *)
(*Set the diagonal of a matrix to 0.*)


zeroDiag[M_]:=M-DiagonalMatrix[Diagonal[M]]


(* ::Text:: *)
(*Create an indicator vector.*)


indicatorVector[i_,n_]:=Insert[ConstantArray[0,n-1],1,i]


(* ::Subsection:: *)
(*Markov Chains*)


(* ::Text:: *)
(*The following function will change any positive valued matrix into a markov chain transition matrix by normalizing the rows.*)


markovTransition[M_]:=Normalize[#,Total]&/@M


(* ::Text:: *)
(*Construct a lazy markov transition matrix for a graph.*)


lazyMarkovTransition[G_]:=1/2 (IdentityMatrix[VertexCount[G]]+Inverse[degreeFromAdjacency[AdjacencyMatrix[G]]].AdjacencyMatrix[G])


(* ::Text:: *)
(*Compute the stationary distribution of a markov chain.*)


statDist[M_]:=Normalize[eigenvectorN[Transpose[M],1]//Re//Abs,Total]


statDistSubset[M_,S_]:=Normalize[
	ReplacePart[statDist[M],(#->0)&/@Complement[Range[Length[M]],S]],
	Total
]


(* ::Text:: *)
(*Get a sample return time for a given state in a markov chain.*)


step[M_,v_]:=RandomChoice[M[[v]]->Range[Length[M]]]


generateReturnPathInt[M_,v_,p_]:=If[Last[p]==v,p,generateReturnPathInt[M,v,Append[p,step[M,Last[p]]]]]


generateReturnPath[M_,v_]:=generateReturnPathInt[M,v,{step[M,v]}]


sampleReturnTime[M_,v_]:=Length[generateReturnPath[M,v]]


sampleVisitsBeforeReturn[M_,v_,u_]:=Count[generateReturnPath[M,v],u]


sampleVisitsWithPathLength[M_,v_,u_]:=With[{p=generateReturnPath[M,v]},{Length[p],Count[p,u]}]


(* ::Text:: *)
(*Compute the conductance of a set of states. Recall that the conductance is the probability that a random walk starting in S immediately leaves S.*)


markovConductance[M_,S_]:=Total[(statDistSubset[M,S].M)[[Complement[Range[Length[M]],S]]]]


(* ::Subsection::Closed:: *)
(*Visualization*)


(* ::Text:: *)
(*Some shortcuts for visualizing graphs and their matrices.*)


plotAdj[G_]:=MatrixPlot[AdjacencyMatrix[G]]


(* ::Text:: *)
(*Get a mapping of the edge weights from a graph. Intended to be passes to EdgeLabels when plotting a graph to display the weights.*)


edgeWeights[G_]:=With[{A=WeightedAdjacencyMatrix[G]},
	(#->A[[#[[1]]]][[#[[2]]]])&/@EdgeList[G]
]


(* ::Text:: *)
(*Plot a graph with a random node layout.*)


randomGraphPlot[G_]:=GraphPlot[G,VertexCoordinates->Table[{RandomReal[],RandomReal[]},{i,1,VertexCount[G]}]]


(* ::Subsection::Closed:: *)
(*General Graph Functions*)


(* ::Text:: *)
(*Compute standard graph theoretic ideas from adjacency matrices.*)


weightFromAdj[A_,s1_,s2_]:=Total[Transpose[A[[s1]]][[s2]],Infinity]


conductanceFromAdj[A_,s_]:=With[{sbar=Complement[Range[Length[A]],s]},weightFromAdj[A,s,sbar]/(weightFromAdj[A,s,sbar]+weightFromAdj[A,s,s])]


(* ::Text:: *)
(*Get the volume of a set of vertices in a graph.*)


setVolume[S_,G_]:=Total[VertexDegree[G][[S]]]


(* ::Text:: *)
(*Get the girth of a graph.*)


girth[G_]:=LengthWhile[Range[VertexCount[G]],(FindCycle[G,#]=={})&]+1


(* ::Subsection::Closed:: *)
(*Clustering*)


(* ::Text:: *)
(*Give an implementation of unnormalised spectral clustering for graphs.*)


spectralClustering[G_,k_,numEigs_]:=FindClusters[
	Thread[Rule[Eigenvectors[laplacian[G]//N,-(numEigs+1)][[1;;-2]]//Transpose,Range[VertexCount[G]]]],
	k,
	Method->"KMeans"
]


spectralClustering[G_,k_]:=spectralClustering[G,k,k]


(* ::Text:: *)
(*Get the symmetric difference between a clustering and the ground truth.*)


symDiff[A_,S_]:=Union[Complement[A,S],Complement[S,A]]


graphSymDiff[G_,A_,S_]:=setVolume[symDiff[A,S],G]


totalSymDiff[G_,clusters_,k_,n_]:=Total[(graphSymDiff[G,clusters[[#]],Range[n*(#-1)+1,n*#]])&/@Range[k]]


(* ::Text:: *)
(*Measure the quality of a clustering with the rand index.*)


sameCluster[clustering_,i_,j_]:=AnyTrue[ContainsAll[#,{i,j}]&/@clustering,#&]


clusteringsAgree[clustering1_,clustering2_,i_,j_]:=If[sameCluster[clustering1,i,j]==sameCluster[clustering2,i,j],1,0]


randIndex[clusters_,gt_]:=With[
	{n=Max[gt],agreeFunc=clusteringsAgree[clusters,gt,#1,#2]&},
	1/Binomial[n,2]*(Total[agreeFunc[#[[1]],#[[2]]]&/@Flatten[Table[{i,j},{i,1,n},{j,i+1,n}],1]])
]


(* ::Subsection::Closed:: *)
(*Bonus*)


(* ::Text:: *)
(*Some miscellaneous functions.*)


(* ::Text:: *)
(*Generate a list of taylor series expansions for a given function.*)


taylorList[f_,x0_,n_]:=(Series[f[x],{x,x0,#}]//Normal)&/@Range[n]


plotTaylors[f_,x0_,n_,min_,max_]:=Plot[{f[y]}~Join~(taylorList[f,x0,n]/.{x->y}),{y,min,max}]


(* ::Text:: *)
(*Randomly permute the rows and columns of a matrix. This can be used as a visual aid to the difficulty of graph algorithms.*)


permuteMatrix[M_]:=With[{s=RandomSample[Range[Length[M]]]},M[[s,s]]]


(* ::Subsection::Closed:: *)
(*Boilerplate*)


(* ::Text:: *)
(*The remaining code is just needed to create the package  correctly.*)


(* ::Input:: *)
(*End[]*)
(*Protect@@Names["prmGraphs`*"];*)
(*EndPackage[]*)
