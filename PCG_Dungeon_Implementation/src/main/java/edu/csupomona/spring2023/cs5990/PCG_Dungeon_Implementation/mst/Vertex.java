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

public class Vertex {
	LinkedList<Vertex> adj;
	int data;
	int color;//0=white, 1=gray, 2=black
	int distance;//from start vertex
	Vertex parent;
	int discoveryTime;
	int finishTime;
	boolean extracted;
	
	public Vertex(int data){
		this.data=data;
		color=0;
		distance=-1;
		parent=null;
		adj = new LinkedList<>();
		discoveryTime=0;
		finishTime=0;
	}
	
	/**
	 * Provides the index of this vertex.
	 * @return The index of this vertex.
	 * @author Payton Perchez
	 */
	public int getIndex()
	{
		return data;
	}
	
	/**
	 * Provides the list of vertices that are adjacent to this one.
	 * @return The list of adjacent vertices.
	 * @author Payton Perchez
	 */
	public LinkedList<Vertex> getAdjacencies()
	{
		return adj;
	}
}