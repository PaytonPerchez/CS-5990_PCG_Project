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

import java.util.Arrays;
import java.util.Comparator;
import java.util.Scanner;

class Checker implements Comparator<int[]>{
	public int compare(int[] o1, int[] o2) {
		return Integer.compare(o1[2], o2[2]);
	}
}

/*
 * Modified original comparator to support custom Edge class.
 * @author Payton Perchez
 */
class Checker2 implements Comparator<Edge>{
	public int compare(Edge e1, Edge e2) {
		return Double.compare(e1.getWeight(), e2.getWeight());
	}
}

public class KruskalMST extends Graph{
	double cost; // changed from int to double by Payton Perchez
	boolean cycle;

	public KruskalMST(int v) {
		super(v);
		cost = 0;
		cycle = false;
	}
	
	/*
	 * Changed the visibility of the original method to public. Takes edges input as an array of Edges
	 * instead of a matrix of integers. Ensured edges were sorted by calling Arrays.sort. Modified
	 * for loop to support iterating through Edges.
	 * @author Payton Perchez
	 */
	public void Kruskal(Edge[] edges){
		Arrays.sort(edges,new Checker2());
		for(Edge edge : edges){
			int a = edge.getVertex1(), b = edge.getVertex2();
			double w = edge.getWeight();
			if(a==b)	continue;//loop
			addEdge(a, b);
			if(!isCycle()){
				cost+=w;
			}else{
				vertex[a].adj.removeLast();
				vertex[b].adj.removeLast();
			}
		}
		System.out.println("Cost: "+cost);
	}
	
	void Kruskal(int[][] edges){
		for(int i = 0; i<edges.length; i++){
			int a = edges[i][0], b = edges[i][1], w = edges[i][2];
			if(a==b)	continue;//loop
			addEdge(a, b);
			if(!isCycle()){
				System.out.println(a+" "+b+" "+w+" added");
				cost+=w;
			}else{
				vertex[a].adj.removeLast();
				vertex[b].adj.removeLast();
			}
		}
		System.out.println("Cost: "+cost);
	}
	
	void reset(){
		for(int i = 0; i<v; i++)
			vertex[i].color = 0;
		cycle = false;
	}
	
	boolean isCycle(){
		reset();
		for(int i=0;i<v && !cycle;i++){
	        if(vertex[i].color==0)
	            DFSVisit(i);
	    }
		return cycle;
	}
	
	void DFSVisit(int u){
		vertex[u].color=1;
		for(Vertex v: vertex[u].adj){
			if(cycle)	break;
			if(v.color==2){//cycle
				cycle = true;
				return;
			}
			if(v.color==0){
				DFSVisit(v.data);
			}
		}
		vertex[u].color=2;
	}
	
	public static void main(String[] args){
		Scanner sc = new Scanner(System.in);
		int v = sc.nextInt();
		int e = sc.nextInt();
		int[][] edges = new int[e][3];
		//edge from a[0] to a[1] with weight a[2]
		for(int i = 0; i<e; i++){
			int a = sc.nextInt(), b = sc.nextInt(), w = sc.nextInt();
			edges[i][0] = a;
			edges[i][1] = b;
			edges[i][2] = w;
		}
		Arrays.sort(edges,new Checker());
		KruskalMST g = new KruskalMST(v);
		g.Kruskal(edges);
		sc.close();
	}
}
/*
SAMPLE CASE
5 8
0 1 1
0 2 4
0 4 2
2 4 3
1 4 3
3 1 3
3 2 1
3 4 2
*/