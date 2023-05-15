package edu.csupomona.spring2023.cs5990.PCG_Dungeon_Implementation.mst;

/**
 * Data structure for representing a weighted edge between two vertices.
 * @author Payton Perchez
 */
public class Edge
{
	private int vertex1;
	private int vertex2;
	private double weight;
	
	/**
	 * Instantiates a new Edge with the specified vertices and weight.
	 * @param vertex1
	 * @param vertex2
	 * @param weight
	 */
	public Edge(int vertex1, int vertex2, double weight)
	{
		this.vertex1 = vertex1;
		this.vertex2 = vertex2;
		this.weight = weight;
	}
	
	public int getVertex1()
	{
		return vertex1;
	}
	
	public int getVertex2()
	{
		return vertex2;
	}
	
	public double getWeight()
	{
		return weight;
	}
	
}// end Edge
