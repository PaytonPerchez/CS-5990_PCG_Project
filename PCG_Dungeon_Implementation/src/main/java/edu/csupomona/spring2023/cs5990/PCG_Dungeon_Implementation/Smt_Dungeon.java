package edu.csupomona.spring2023.cs5990.PCG_Dungeon_Implementation;

import javafx.application.Application;
import javafx.stage.Stage;
import javafx.scene.Scene;
import javafx.scene.layout.HBox;
import javafx.scene.paint.Color;
import javafx.scene.shape.Rectangle;
import javafx.scene.shape.Polyline;
import javafx.scene.control.Button;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Random;
import java.util.stream.IntStream;

//import javax.print.attribute.standard.NumberOfInterveningJobs;

//import org.sosy_lab.java_smt.SolverContextFactory;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Context;
import com.microsoft.z3.Model;
import com.microsoft.z3.Status;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.IntExpr;

// The only methods that use the below libraries are draw_rooms, create_graph_array, draw_passageways
import edu.csupomona.spring2023.cs5990.PCG_Dungeon_Implementation.delaunay.*;
import edu.csupomona.spring2023.cs5990.PCG_Dungeon_Implementation.mst.*;

/*
 * Z3 Resources:
 * 
 * https://github.com/Z3Prover/z3/blob/master/examples/java/JavaExample.java
 * https://z3prover.github.io/api/html/classcom_1_1microsoft_1_1z3_1_1_solver.html
 * https://ericpony.github.io/z3py-tutorial/guide-examples.htm
 */

/**
 * Java implementation of Jim Whitehead's procedural dungeon generation algorithm
 * Source: (https://github.com/JimWhiteheadUCSC/smt_dungeon)
 * @author Jack Peabody
 * @author Payton Perchez
 */
public class Smt_Dungeon extends Application
{
	private		final	int			NUM_ROOMS			= 30;			// Default number of rooms
	private				int			number_of_rooms		= NUM_ROOMS;	// The number of rooms (which the user can change)
	private		final	int			SCALE_FACTOR		= 1000;
	private		final	int			ROOM_WIDTH_MIN		= 10;
	private		final	int			ROOM_WIDTH_MAX		= 20;
	private		final	int			ROOM_HEIGHT_MIN		= 10 * SCALE_FACTOR;
	private		final	int			ROOM_HEIGHT_MAX		= 20 * SCALE_FACTOR;
	private		final	int			CANVAS_WIDTH		= 400;
	private		final	int			CANVAS_HEIGHT		= 400;
	private		final	int			SEPARATION			= 10;			// Units between room borders
	private		final	int			SEPARATION_Y		= SEPARATION * SCALE_FACTOR;
	private		final	int			BORDER				= 5;
	private		final	int			LINEWIDTH			= 30;
	private		final	int			LINEWIDTH_Y			= LINEWIDTH * SCALE_FACTOR;
	private		final	int			EXCEPTION_RATE		= 0;
	private		final	int			GRID_CELL			= 5;
	private		final	int			GRID_CELL_Y			= GRID_CELL * SCALE_FACTOR;
	private				int[]		gridCounts;
	private		final	int			NUM_LOOPS			= 5;
	private		final	int			NUM_RUNS			= 25;
	private		final	int			PASSAGE_WIDTH		= 3;
	private				boolean		quadConstraints		= false;
	private				boolean		lineConstraints		= false;
	private				boolean		big_room_constraint	= false;
	private				boolean		showDelaunay		= false;
	private				boolean		showSparse			= false;
	private 			ArrayList<Room> rooms;
	private				int[]		assumptions;
//	private		static	HashMap<String, String> directions = new HashMap<>();
//	static
//	{
//		directions.put("vert", "above");
//		directions.put("vert", "above");
//	}
	private				int			and_clause_count		= 0;
	private				int			or_clause_count		= 0;
	private				boolean		runOnce				= false;	// only runs the program once if true
	private				boolean		looper				= true;		// keeps the program running
	
	private				Solver		solver;
	private				Context		ctx;
	
	public static void main(String[] args)
	{
		//-Djava.library.path=C:\Users\payto\MySoftware\z3-4.12.1-x64-win\bin\libz3java.dll
//		System.setProperty("java.library.path", "C:/Users/payto/MySoftware/z3-4.12.1-x64-win/bin/libz3java.dll");
		launch(args);
	}


	public void init_rooms(){
		// Change this to use Z3 Int() type?
		rooms = new ArrayList<>();
		for(int i = 0; i < number_of_rooms; i++){
			Room r = new Room(ctx, i);
			if((int) ((Math.random() * 101) + 1) <= EXCEPTION_RATE){
				//Random random = new Random();
				//r.setWidth(random.nextInt(ROOM_WIDTH_MAX*4 - ROOM_WIDTH_MIN*4) + (ROOM_WIDTH_MAX*4 - ROOM_WIDTH_MIN*4));
				r.setWidth((int) ((Math.random() * ((ROOM_WIDTH_MAX * 4) - (ROOM_WIDTH_MIN * 4) + 1)) + (ROOM_WIDTH_MIN * 4)));
				r.setHeight((int) ((Math.random() * ((ROOM_HEIGHT_MAX * 4) - (ROOM_HEIGHT_MIN * 4) + 1)) + (ROOM_HEIGHT_MIN * 4)));
			}
			else{
				r.setWidth((int) ((Math.random() * (ROOM_WIDTH_MAX - ROOM_WIDTH_MIN + 1)) + ROOM_WIDTH_MIN));
				r.setHeight((int) ((Math.random() * (ROOM_HEIGHT_MAX - ROOM_HEIGHT_MIN + 1)) + ROOM_HEIGHT_MIN));
			}
			r.setQuad(1);
			rooms.add(r);
		}
	}

	public void create_big_room_constraints(Solver slv){
		/*
		 * Make the first room 20% of the size of the playfield, and constrain its placement
		 */
		rooms.get(0).setWidth((int) (0.4 * CANVAS_WIDTH));
		rooms.get(0).setHeight((int) (0.6 * CANVAS_WIDTH * SCALE_FACTOR));

		// I don't know if this warning matters
		slv.add(ctx.mkAnd(
			//rooms.get(0).get("x") >= 0.3 * CANVAS_WIDTH,
			ctx.mkGe(rooms.get(0).getX(), ctx.mkReal(3 * CANVAS_WIDTH, 10)),
			
			//rooms.get(0).get("x") <= 0.35 * CANVAS_WIDTH,
			ctx.mkLe(rooms.get(0).getX(), ctx.mkReal(35 * CANVAS_WIDTH, 100)),
			
			//rooms.get(0).get("y") >= 0.1 * CANVAS_HEIGHT * SCALE_FACTOR,
			ctx.mkGe(rooms.get(0).getY(), ctx.mkReal(CANVAS_WIDTH, 10)),
			
			//rooms.get(0).get("y") <= 0.25 * CANVAS_HEIGHT * SCALE_FACTOR
			ctx.mkLe(rooms.get(0).getY(), ctx.mkReal(CANVAS_WIDTH, 4))
		));

		and_clause_count = and_clause_count + 4;
		or_clause_count = or_clause_count + 0;

		// Antechamber
		rooms.get(1).setWidth((int) (0.4 * CANVAS_WIDTH));
		rooms.get(1).setHeight((int) (0.05 * CANVAS_WIDTH * SCALE_FACTOR));
		rooms.get(2).setWidth(15);
		rooms.get(2).setWidth(15 * SCALE_FACTOR);
	}

	public void create_separation_contraints(Solver slv){
		for(int i = 0; i < number_of_rooms; i++){
			for(int j = i + 1; j < number_of_rooms; j++){
				if(big_room_constraint){
					if(i == 0 && (j == 1 || j == 2)){
						// TODO add_big_room_separation_constraint(slv, i, j);
					}
					else{
						// TODO add_separation_constraint(slv, i, j);
					}
				}
				else{
					// TODO add_separation_constraint(slv, i, j);
				}
			}
		}
	}

	public void create_canvas_constraints(Solver slv){
		for(int i = 0; i < number_of_rooms; i++){
			slv.add(
				ctx.mkGe(rooms.get(i).getX(), ctx.mkInt(0)),
				ctx.mkLe(ctx.mkAdd(rooms.get(i).getX(), ctx.mkInt(rooms.get(i).getWidth())), ctx.mkInt(CANVAS_WIDTH))
			);
			slv.add(
				ctx.mkGe(rooms.get(i).getY(), ctx.mkInt(0)),
				ctx.mkLe(ctx.mkAdd(rooms.get(i).getY(), ctx.mkInt(rooms.get(i).getHeight())), ctx.mkInt(CANVAS_HEIGHT * SCALE_FACTOR))
			);
			and_clause_count = and_clause_count + 4;
			or_clause_count = or_clause_count + 0;
		}
	}

	public void create_line_constraints(Solver slv){
		for(int i = 0; i < number_of_rooms; i++){
			slv.add(ctx.mkOr(
				ctx.mkAnd(
					ctx.mkGe(ctx.mkAdd(rooms.get(i).getY(), rooms.get(i).getX()), ctx.mkInt(380 - LINEWIDTH)),
					ctx.mkLe(ctx.mkAdd(rooms.get(i).getY(), rooms.get(i).getX()), ctx.mkInt(380 + LINEWIDTH))),
				ctx.mkAnd(
					ctx.mkGe(rooms.get(i).getX(), ctx.mkSub(rooms.get(i).getY(), ctx.mkInt(LINEWIDTH))),
					ctx.mkLe(rooms.get(i).getX(), ctx.mkAdd(rooms.get(i).getY(), ctx.mkInt(LINEWIDTH))))
			));
			and_clause_count = and_clause_count + 4;
			or_clause_count = or_clause_count + 2;
		}
	}

	public void create_point_line_constraints(){

	}

	public void create_mousepoint_constraints(){

	}

	public void create_quad_constraints(Solver slv){
		for(int i = 0; i < number_of_rooms; i++){
			// upper left
			if(rooms.get(i).getQuad() == 1){
				slv.add(ctx.mkAnd(
					ctx.mkLe(rooms.get(i).getX(), ctx.mkInt((CANVAS_WIDTH / 2) - rooms.get(i).getWidth())),
					ctx.mkLe(rooms.get(i).getY(), ctx.mkInt((CANVAS_HEIGHT / 2) - rooms.get(i).getHeight()))
				));
			}
			// upper right
			if(rooms.get(i).getQuad() == 2){
				slv.add(ctx.mkAnd(
					ctx.mkGt(rooms.get(i).getX(), ctx.mkInt(CANVAS_WIDTH / 2)),
					ctx.mkLe(rooms.get(i).getY(), ctx.mkInt((CANVAS_HEIGHT / 2) - rooms.get(i).getHeight()))
				));
			}
			// lower left
			if(rooms.get(i).getQuad() == 3){
				slv.add(ctx.mkAnd(
					ctx.mkLe(rooms.get(i).getX(), ctx.mkInt((CANVAS_WIDTH / 2) - rooms.get(i).getWidth())),
					ctx.mkGe(rooms.get(i).getY(), ctx.mkInt(CANVAS_HEIGHT / 2))
				));
			}
			// lower right
			if(rooms.get(i).getQuad() == 4){
				slv.add(ctx.mkAnd(
					ctx.mkGt(rooms.get(i).getX(), ctx.mkInt(CANVAS_WIDTH / 2)),
					ctx.mkGe(rooms.get(i).getY(), ctx.mkInt(CANVAS_HEIGHT / 2))
				));
			}
			and_clause_count = and_clause_count + 2;
			or_clause_count = or_clause_count + 0;
		}
	}

	/**
	 * Computes the centerpoints for each room in the given Model.
	 * @param m The given Model.
	 * @return An array of centerpoints.
	 */
	public float[][] compute_room_centerpoints(Model m)
	{
		float[][] cp = new float[rooms.size()][2];
		
		for(int i = 0; i < number_of_rooms; i++){
			// rooms.get(i).getX() and rooms.get(i).getY() are integer constant names in the Model m
			// add new 'center' records to each room
			rooms.get(i).setCenterX(Integer.parseInt(m.getConstInterp(rooms.get(i).getX()).toString()) + (rooms.get(i).getWidth() / 2f));
			rooms.get(i).setCenterY(Integer.parseInt(m.getConstInterp(rooms.get(i).getY()).toString()) + (rooms.get(i).getHeight() / 2f));
			
			cp[i] = new float[] {rooms.get(i).getCenterX(), rooms.get(i).getCenterY()};
		}
		
		return cp;
	}

	// TODO implement draw_rooms, draw_lines, and draw_passageways
	private void drawRooms(Model m, DelaunayTriangulator tri, int[][] mst, float[][] centerPoints, ArrayList<double[]> mousePoints)
	{
		Rectangle rectangle;
		for(int i = 0; i < number_of_rooms; i++)
		{
			rectangle = new Rectangle(
				(Integer.parseInt(m.getConstInterp(rooms.get(i).getX()).toString()) + BORDER),
				((Integer.parseInt(m.getConstInterp(rooms.get(i).getY()).toString()) / SCALE_FACTOR) + BORDER),
				rooms.get(i).getWidth(),
				(rooms.get(i).getHeight() / SCALE_FACTOR)
			);
			rectangle.setStrokeWidth(2);
			
			switch(rooms.get(i).getQuad())
			{
			case 1:
				// Default color of rectangle is already black
				break;
			case 2:
				rectangle.setFill(Color.rgb(255, 133, 27));	// orange
				break;
			case 3:
				rectangle.setFill(Color.rgb(0, 116, 217));	// blue
				break;
			case 4:
				rectangle.setFill(Color.rgb(46, 204, 64));	// green
				break;
			default:
				break;
			}// end switch
			
		}// end for
		
		if(tri != null)
		{
			if(showDelaunay)
			{
				Polyline lines = new Polyline();
				lines.setStroke(Color.rgb(0, 45, 225));	// dark blue
				
				// Draw Delaunay triangulation
				for(Triangle2D triangle : tri.getTriangles())
				{
					//System.out.println("t is " + triangle);
					// TODO convert points to int??
					lines.getPoints().addAll(
						(triangle.a.x + BORDER), (triangle.a.y / SCALE_FACTOR) + BORDER,
						(triangle.b.x + BORDER), (triangle.b.y / SCALE_FACTOR) + BORDER,
						(triangle.c.x + BORDER), (triangle.c.y / SCALE_FACTOR) + BORDER
					);
				}
				
				lines.getPoints().addAll(
					lines.getPoints().get(0),
					lines.getPoints().get(1)
				);
//				SOMENODE.getChildren().add(lines);
			}
			
		}// end if
		
		if(mst != null)
		{
			if(showSparse)
			{
				Polyline lines = new Polyline();
				lines.setStroke(Color.rgb(0, 225, 0));	// lime green
				// TODO convert points to int??
				for(int[] points : mst)
				{
					lines.getPoints().addAll(
						(double) centerPoints[points[0]][0] + BORDER,
						(double) (centerPoints[points[0]][1] / SCALE_FACTOR) + BORDER,
						(double) centerPoints[points[1]][0] + BORDER,
						(double) (centerPoints[points[1]][2] / SCALE_FACTOR) + BORDER
					);
				}
				lines.getPoints().addAll(
					lines.getPoints().get(0),
					lines.getPoints().get(1)
				);
//				SOMENODE.getChildren().add(lines);
			}
		}
		
		if(!mousePoints.isEmpty())
		{
			Polyline lines = new Polyline();
			lines.setStroke(Color.rgb(139, 0, 0));	// dark red
			for(double[] points : mousePoints)
			{
				lines.getPoints().addAll(points[0], points[1]);
			}
//			SOMENODE.getChildren().add(lines);
		}
		
		drawPassageways(m, mst);
		
	}// end drawRooms
	
	
	private void drawPassageways(Model m, int[][] mst)
	{
		Random random = new Random();
		int top;
		int bottom;
		int left;
		int right;
		int[] overlap;
		int passX;
		int passY;
		
		for(int[] points : mst)
		{
			// Determine which room is above the other room
			if(Integer.parseInt(m.getConstInterp(rooms.get(points[0]).getY()).toString()) < Integer.parseInt(m.getConstInterp(rooms.get(points[1]).getY()).toString()))
			{
				top = points[0];
				bottom = points[1];
				
			} else {
				
				top = points[1];
				bottom = points[0];
			}
			
			// Determine which room is to right of other room
			if(Integer.parseInt(m.getConstInterp(rooms.get(points[0]).getX()).toString()) < Integer.parseInt(m.getConstInterp(rooms.get(points[1]).getX()).toString()))
			{
				left = points[0];
				right = points[1];
				
			} else {
				
				right = points[0];
				left = points[1];
			}
			
			int[] top_x_range = new int[] {Integer.parseInt(m.getConstInterp(rooms.get(top).getX()).toString()) + PASSAGE_WIDTH, Integer.parseInt(m.getConstInterp(rooms.get(top).getX()).toString()) + rooms.get(top).getWidth() - PASSAGE_WIDTH};
			int[] top_y_range = new int[] {Integer.parseInt(m.getConstInterp(rooms.get(top).getY()).toString()) + PASSAGE_WIDTH, Integer.parseInt(m.getConstInterp(rooms.get(top).getY()).toString()) + rooms.get(top).getHeight() - PASSAGE_WIDTH};
			int[] bottom_x_range = new int[] {Integer.parseInt(m.getConstInterp(rooms.get(bottom).getX()).toString()) + PASSAGE_WIDTH, Integer.parseInt(m.getConstInterp(rooms.get(bottom).getX()).toString()) + rooms.get(bottom).getWidth() - PASSAGE_WIDTH};
			int[] bottom_y_range = new int[] {Integer.parseInt(m.getConstInterp(rooms.get(bottom).getY()).toString()) + PASSAGE_WIDTH, Integer.parseInt(m.getConstInterp(rooms.get(bottom).getY()).toString()) + rooms.get(bottom).getHeight() - PASSAGE_WIDTH};
			
			Polyline lines = new Polyline();
			lines.setStrokeWidth(PASSAGE_WIDTH);
			
			if(rangeOverlapping(top_x_range, bottom_x_range))
			{
				if(rangeOverlapping(top_y_range, bottom_y_range))
				{
					System.out.println("Rooms overlapping??");
					
				} else {
					
					// x overlap, no y overlap. Drop passage down from top room to bottom room
					overlap = overlap(top_x_range, bottom_x_range);
					passX = overlap[random.nextInt(overlap.length)];
					lines.getPoints().addAll(
						(double) passX + BORDER, (double) (((Integer.parseInt(m.getConstInterp(rooms.get(top).getY()).toString()) + rooms.get(top).getHeight()) / SCALE_FACTOR) + BORDER),
						(double) passX + BORDER, (double) ((Integer.parseInt(m.getConstInterp(rooms.get(bottom).getY()).toString()) / SCALE_FACTOR) + BORDER)
					);
					
//					SOMENODE.getChildren().add(lines);
				}
				
			} else {
				
				if(rangeOverlapping(top_y_range, bottom_y_range))
				{
					// y overlap, no x overlap, draw line straight across
					overlap = overlap(top_y_range, bottom_y_range);
					passY = overlap[random.nextInt(overlap.length)];
					lines.getPoints().addAll(
						(double) (Integer.parseInt(m.getConstInterp(rooms.get(left).getX()).toString()) + rooms.get(left).getWidth() + BORDER), (double) ((passY / SCALE_FACTOR) + BORDER),
						(double) (Integer.parseInt(m.getConstInterp(rooms.get(right).getX()).toString()) + BORDER), (double) ((passY / SCALE_FACTOR) + BORDER)
					);
					
//					SOMENODE.getChildren().add(lines);
					
				} else {
					
					// no x overlap, no y overlap, draw right-angle connector
					passX = random.nextInt(bottom_x_range[1] - bottom_x_range[0]) + bottom_x_range[0];
					passY = random.nextInt(top_y_range[1] - top_y_range[0]) + top_y_range[0];
					if(top == left)
					{
						lines.getPoints().addAll(
							(double) (Integer.parseInt(m.getConstInterp(rooms.get(top).getX()).toString()) + rooms.get(top).getWidth() + BORDER), (double) ((passY / SCALE_FACTOR) + BORDER)
						);
						
					} else {
						
						lines.getPoints().addAll(
							(double) (Integer.parseInt(m.getConstInterp(rooms.get(top).getX()).toString()) + BORDER),
							(double) ((passY / SCALE_FACTOR) + BORDER)
						);
					}
					
					lines.getPoints().addAll(
						(double) (passX + BORDER + (PASSAGE_WIDTH / 2)), (double) ((passY / SCALE_FACTOR) + BORDER)
					);
					
//					SOMENODE.getChildren().add(lines);
					lines = new Polyline();
					lines.setStrokeWidth(PASSAGE_WIDTH);
					
					lines.getPoints().addAll(
						(double) (passX + BORDER), (double) ((passY / SCALE_FACTOR) + BORDER),
						(double) (passX + BORDER), (double) (Integer.parseInt(m.getConstInterp(rooms.get(bottom).getY()).toString()) / SCALE_FACTOR)
					);
//					SOMENODE.getChildren().add(lines);
					
				}// end if
				
			}// end if
			
		}// end for
		
	}// end drawPassageways
	
	
	private boolean rangeOverlapping(int[] range1, int[] range2)
	{
		if((range1[0] == range1[1]) || (range2[0] == range2[1]))
		{
			return false;
			
		} else {
			
			return (((range1[0] < range2[1]) && (range1[1] > range2[0])) ||
					((range1[1] > range2[0]) && (range2[1] > range1[0])));
		}
	}
	
	
	private int[] overlap(int[] range1, int[] range2)
	{
		if(!rangeOverlapping(range1, range2))
		{
			return new int[] {};
			
		} else {
			
			return IntStream.rangeClosed(Math.max(range1[0], range2[0]), Math.min(range1[1], range2[1]) + 1).toArray();
		}
	}
	
	/**
	 * Computes the distance between the two given points.
	 * @param point1 Float array in the form [x1, y1].
	 * @param point2 Float array in the form [x2, y2].
	 * @return The distance between the two given points
	 */
	private double distance(float[] point1, float[] point2)
	{
		return Math.sqrt(Math.pow((point2[0] - point1[0]), 2) + Math.pow((point2[1] - point1[1]) / SCALE_FACTOR, 2));
	}
	
	/**
	 * Computes the distance between the two given points.
	 * @param point1 Vector containing x1 and y1.
	 * @param point2 Vector containing x2 and y2.
	 * @return The distance between the two given points
	 */
	private double distance(Vector2D point1, Vector2D point2)
	{
		return Math.sqrt(Math.pow((point2.x - point1.x), 2) + Math.pow((point2.y - point1.y) / SCALE_FACTOR, 2));
	}
	
	/**
	 * Creates 2D array (matrix) representing the given triangulation.
	 * @param tri The given triangulation.
	 * @param cp The set of points in the triangulation. TODO consider removing this argument.
	 * @param edges The set of edges in the triangulation.
	 * @return The matrix containing distances between points (rows/columns) in the given triangulation.
	 */
	private double[][] create_graph_array(DelaunayTriangulator tri, float[][] cp, ArrayList<Edge> edges)
	{
		double[][] graph = new double[rooms.size()][rooms.size()];
		
		for(Triangle2D t : tri.getTriangles())
		{
			// Prevent duplicate edges/distances
			if(t.a.index < t.b.index)
			{
//				graph[t.a.index][t.b.index] = distance(cp[t.a.index], cp[t.b.index]);
				graph[t.a.index][t.b.index] = distance(t.a, t.b);
				edges.add(new Edge(t.a.index, t.b.index, graph[t.a.index][t.b.index]));
			}
			
			// Prevent duplicate edges/distances
			if(t.b.index < t.c.index)
			{
//				graph[t.b.index][t.c.index] = distance(cp[t.b.index], cp[t.c.index]);
				graph[t.b.index][t.c.index] = distance(t.b, t.c);
				edges.add(new Edge(t.b.index, t.c.index, graph[t.b.index][t.c.index]));
			}
			
			// Prevent duplicate edges/distances
			if(t.c.index < t.a.index)
			{
//				graph[t.c.index][t.a.index] = distance(cp[t.c.index], cp[t.a.index]);
				graph[t.c.index][t.a.index] = distance(t.c, t.a);
				edges.add(new Edge(t.c.index, t.a.index, graph[t.c.index][t.a.index]));
			}
			
		}// end for
		
		return graph;
		
	}// end create_graph_array
	
	/**
	 * Converts the given points to vectors.
	 * @param points The given points in the format [[x1, y1], ..., [xn, yn]].
	 * @return The list of converted points.
	 */
	private ArrayList<Vector2D> convertPointsToVectors(float[][] points)
	{
		ArrayList<Vector2D> vectors = new ArrayList<>(points.length);
		
		for(int i = 0; i < points.length; i++)
		{
			vectors.add(new Vector2D(points[i][0], points[i][1], i));
		}
		
		return vectors;
	}
	
	/**
	 * Parses the given list of vertices into pairs of adjacent vertices.
	 * @param vertices The given list of vertices.
	 * @return The pairs of adjacent vertices.
	 */
	private int[][] getMst(Vertex[] vertices)
	{
		HashMap<Integer, ArrayList<Integer>> uniqueAdjacencies = new HashMap<>();
		int adjacencyCount = 0;		// the number of pairs
		
		for(Vertex currentVertex : vertices)
		{
			uniqueAdjacencies.put(currentVertex.getIndex(), new ArrayList<>());
			
			for(Vertex adjacentVertex : currentVertex.getAdjacencies())
			{
				// Prevent duplicate pairs (combinations)
				if(!uniqueAdjacencies.containsKey(adjacentVertex.getIndex()))
				{
					uniqueAdjacencies.get(currentVertex.getIndex()).add(adjacentVertex.getIndex());
					adjacencyCount++;
				}
			}
		}
		
		int[][] pairs = new int[adjacencyCount][2];
		int currentVertex = 0;
		
		for(Map.Entry<Integer, ArrayList<Integer>> adjacencies : uniqueAdjacencies.entrySet())
		{
			for(int adjacentVertex = 0; adjacentVertex < adjacencies.getValue().size(); adjacentVertex++)
			{
				pairs[currentVertex + adjacentVertex] = new int[] {adjacencies.getKey(), adjacencies.getValue().get(adjacentVertex)};
			}
			currentVertex++;
		}
		
		return pairs;
		
	}// end getMst
	
	@Override
	public void start(Stage primaryStage)
	{
		// main starts here
		System.out.println("Dungeon layout using SMT");
		int loopCount = NUM_LOOPS;			// set loop count to default
		int runCount = NUM_RUNS;			// set run count to default
		int unsatCount = 0;
		
		// TODO delete after moving the following while loop out of the application thread
		looper = false;						// keeps the program running
		runOnce = false;					// only runs the program once if true
		
		// format: [[x1, y1], [x2, y2], ..., [xn, yn]]
		float[][] centerPoints;
		
//		initGridCounts();					// counts the number of grid cells within the play area
		DelaunayTriangulator tri;
		ArrayList<double[]> mousepoints = new ArrayList<>();	// data structure containing points for control lines specified by the user
		HashMap<String, Long> timingInfo = new HashMap<>();
		
		long begin;
		long end;
		int i;
		
		while(looper)
		{
			if(runOnce)
			{
//				time.sleep(1);
				begin = System.currentTimeMillis();
				Status s = solver.check();
				end = System.currentTimeMillis();
				System.out.println(s);
				System.out.println("Solve time: " + ((end - begin) * 1000) + " ms");
				// Traversing statistics
				BoolExpr[] asrts = solver.getAssertions();
				System.out.println("@@@ Assertions @@@");
				i = 0;
				for(BoolExpr asrt : asrts)
				{
					i = i + 1;
					// System.out.println("Assertion: " + asrt);
				}
				System.out.println("Total assertions: " + i);
				timingInfo.put("solveTime", end - begin);
				// if the solver found a satisfiable layout, display it to the user
				if(s.toInt() == 1)
				{
					//displayRoomPlusModel(solver.model);
					begin = System.currentTimeMillis();
					centerPoints = compute_room_centerpoints(solver.getModel());
					tri = new DelaunayTriangulator(convertPointsToVectors(centerPoints));	// use center points of rooms to initialize Delaunay object
					end = System.currentTimeMillis();
//					timing_info['delaunay_time'] = end - begin
					begin = System.currentTimeMillis();
					ArrayList<Edge> edges = new ArrayList<>();
					double[][] ar = create_graph_array(tri, centerPoints, edges);	// create matrix containing length of edges between nodes of Delaunay triangulation
					KruskalMST graph = new KruskalMST(rooms.size());
					graph.Kruskal(edges.toArray(new Edge[edges.size()]));
					int[][] tcsr = getMst(graph.getVertices());		// get the "compressed-sparse representation of the undirected minimum spanning tree"
					end = System.currentTimeMillis();
//					timing_info['mst_time'] = end - begin
					drawRooms(solver.getModel(), tri, tcsr, centerPoints, mousepoints);
//					update_grid(solver.model());
//					loopCount -= 1;
//					updateTiming();
//					if(loopCount <= 0)
//					{
//						//saveAccumulatedTiming();
//						runCount -= 1;
//						System.out.print("#######\nRun: " + runCount + "\n#######\n");
//						if(runCount <= 0)
//						{
//							looper = false;
//							makeHeatmap();
//							finalDataAnalysis();
//							
//						} else {
//							
//							initRooms();
//							displayRoomInfo();
//							solver = Solver();
//							initAllConstraints(solver, mousepoints);
//							loopCount = NUM_LOOPS;
//						}
//						
//					}// end if
//					
//				} else {
//					
//					System.out.println("Cannot find room placement!");
//					displayRoomInfo();
//					initRooms();
//					loopCount = NUM_LOOPS;
//					unsatCount += 1;
//					if(unsatCount > 10)
//					{
//						primaryStage.close();
//						System.exit(0);
//					}
//					
				}// end if
				
			}// end if
			
		}// end while
		
		Button testButton = new Button("Test");
		testButton.setOnAction(event ->
		{
			System.out.println("yoyoyo");
			ctx = new Context();
			solver = ctx.mkSolver();
			System.out.println(solver.check());
		});
		// --module-path C:\Users\payto\Downloads\javafx-sdk-11.0.2\lib --add-modules=javafx.controls
		Scene scene = new Scene(new HBox(testButton), CANVAS_WIDTH + 2*BORDER, CANVAS_HEIGHT + 2*BORDER);
		primaryStage.setScene(scene);
		primaryStage.setTitle("");
		primaryStage.show();
		
		primaryStage.setOnCloseRequest(e ->
		{
			if(ctx != null)
			{
				ctx.close();
			}
		});
		
		scene.setOnKeyTyped(event ->
		{
			// below are controls for using the program
			switch(event.getCode())
			{
			// run the program if the user presses 'space'
			case SPACE:
//				initRooms();								// initialize dungeon rooms with their dimensions
				ctx = new Context();
				solver = ctx.mkSolver();
//				initAllConstraints(solver, mousepoints);	// add all constraints to the solver
				// commented code from original is ommited
				runOnce = true;
				break;
				
			case ESCAPE:
				looper = false;
				break;
				
			case L:
				lineConstraints = !lineConstraints;
				break;
				
			case EQUALS:
				number_of_rooms += 1;
				break;
				
			case MINUS:
				number_of_rooms -= 1;
				break;
				
			case D:
				showDelaunay = !showDelaunay;
				break;
				
			case S:
				showSparse = !showSparse;
				break;
				
			case U:
//				saveMousepointData(mousepoints);
				break;
				
			case I:
//				mousepoints = loadMousepointData();
				break;
				
//			case Z:
//				break;
				
			default:
				break;
			}// end switch
		});
		
		// if the mouse is being used to create points, use the points for control lines
		scene.setOnMouseClicked(event ->
		{
//			if event.button == 1
//				mousepoints.append(event.pos);
//				System.out.println("Added: " + event.pos);
//				drawLines(surface, mousepoints);
		});
	}// end start
	
}// end Smt_Dungeon
