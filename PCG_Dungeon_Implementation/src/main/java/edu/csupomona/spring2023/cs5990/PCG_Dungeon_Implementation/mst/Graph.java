/*
MIT License

Copyright (c) 2017 Keval Morabia

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

GitHub: https://github.com/kevalmorabia97/Graph-Theory-Implementations-in-Java/tree/master/src
*/

package edu.csupomona.spring2023.cs5990.PCG_Dungeon_Implementation.mst;

import java.util.LinkedList;

public class Graph {//undirected graph
	int v;//no of vertices
	Vertex[] vertex;
	
	public Graph(int v){
		this.v=v;
		vertex = new Vertex[v];
		for(int i = 0; i<v; i++){
			vertex[i] = new Vertex(i);
		}
	}
	
	void addEdge(int a, int b){
		vertex[a].adj.add(vertex[b]);
		if(a!=b)//otherwise 2 times added
			vertex[b].adj.add(vertex[a]);//remove this line for directed graph
	}
	
	void printList(LinkedList<Vertex> l){
		for(Vertex v: l){
			System.out.print(v.data+" ");
		}
		System.out.println();
	}
	
	void printAdjacencyList(){
		for(Vertex v: vertex){
			System.out.print("Vertex "+v.data+": ");
			printList(v.adj);
		}
	}
	
	/**
	 * Provides the vertices of the minimum spanning tree.
	 * @return The vertices of the minimum spanning tree.
	 * @author Payton Perchez
	 */
	public Vertex[] getVertices()
	{
		return vertex;
	}
	
	static void main(String[] args) {
		Graph g = new Graph(5);
		g.addEdge(0, 1);
		g.addEdge(1, 2);
		g.addEdge(2, 0);
		g.addEdge(3, 3);
		g.addEdge(4, 2);
		g.printAdjacencyList();
	}

}