package edu.csupomona.spring2023.cs5990.PCG_Dungeon_Implementation;

import javafx.application.Application;
import javafx.application.Platform;
import javafx.stage.FileChooser;
import javafx.stage.Stage;
import javafx.scene.Scene;
import javafx.scene.Group;
import javafx.scene.layout.HBox;
import javafx.scene.layout.VBox;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.Pane;
import javafx.scene.paint.Color;
import javafx.scene.shape.Rectangle;
import javafx.scene.shape.Polyline;
import javafx.scene.shape.Line;
import javafx.scene.control.Label;
import javafx.scene.control.Button;
import javafx.scene.control.Spinner;
import javafx.scene.control.RadioButton;
import javafx.concurrent.Task;
import javafx.geometry.Pos;
import javafx.scene.input.MouseButton;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.FileNotFoundException;
import java.util.Scanner;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Random;
import java.util.stream.IntStream;

import javax.imageio.ImageIO;

//import javax.print.attribute.standard.NumberOfInterveningJobs;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Context;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.Model;
import com.microsoft.z3.Status;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Z3Exception;

import org.jfree.chart.plot.PlotOrientation;
import org.jfree.data.xy.DefaultIntervalXYDataset;
import org.jfree.data.general.DefaultHeatMapDataset;
import org.jfree.data.general.HeatMapUtils;
import org.jfree.chart.renderer.GrayPaintScale;
import org.jfree.chart.ChartFactory;
import org.jfree.svg.SVGGraphics2D;
import org.jfree.svg.SVGUtils;

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
	private		final	int			NUM_ROOMS			= 15;			// Default number of rooms
	private				int			numberOfRooms		= NUM_ROOMS;	// Number of rooms (which the user can change)
	private		final	int			SCALE_FACTOR		= 1000;			// Verical scale factor for using floating point numbers < 1 with Z3
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
	private		final	int			EXCEPTION_RATE		= 0;
	private		final	int			GRID_CELL			= 5;
	private		final	int			GRID_CELL_Y			= GRID_CELL * SCALE_FACTOR;
	private				int[][]		gridCounts;
	private		final	int			NUM_LOOPS			= 5;			// Default number of layouts to solve per run
	private		final	int			NUM_RUNS			= 5;			// Default number of times to create new constraints
	private		final	int			PASSAGE_WIDTH		= 3;
	private				boolean		quadConstraints		= false;
	private				boolean		lineConstraints		= false;
	private				boolean		bigRoomConstraint	= false;
	private				boolean		showDelaunay		= false;
	private				boolean		showSparse			= false;
	private 			ArrayList<Room> rooms;
//	private		static	HashMap<String, String> directions = new HashMap<>();
//	static
//	{
//		directions.put("vert", "above");
//		directions.put("vert", "above");
//	}
	private				int			andClauseCount		= 0;
	private				int			orClauseCount		= 0;
	
	private				Solver		solver;
	private				Context		ctx;
	
	private				Thread		solverThread;
	
	private				int			loopCount;
	private				int			runCount;

	private HashMap<String, Long> timingInfo;
	private HashMap<String, ArrayList<Long>> accumulatedTimingInfo;
	
	public static void main(String[] args)
	{
		launch(args);
	}

	/**
	 * Initializes the dimensions of all rooms.
	 */
	private void initRooms(){
		
		rooms = new ArrayList<>();
		for(int i = 0; i < numberOfRooms; i++){
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
	
	/**
	 * Computes the centerpoints for each room in the given Model.
	 * @param m The given Model.
	 * @return An array of centerpoints.
	 */
	private float[][] computeRoomCenterpoints(Model m)
	{
		float[][] cp = new float[numberOfRooms][2];
		
		for(int i = 0; i < numberOfRooms; i++){
			// rooms.get(i).getX() and rooms.get(i).getY() are integer constant names in the Model m
			// store center coordinates to each room
			rooms.get(i).setCenterX(valueOf(m, rooms.get(i).getX()) + (rooms.get(i).getWidth() / 2f));
			rooms.get(i).setCenterY((valueOf(m, rooms.get(i).getY()) + (rooms.get(i).getHeight() / 2f)) / (float) SCALE_FACTOR);
			cp[i] = new float[] {rooms.get(i).getCenterX(), rooms.get(i).getCenterY()};
		}
		
		return cp; // TODO may not need (use rooms.get(i).getCenterX/Y instead?)
	}

	/**
	 * Make the first room 20% of the size of the playfield, and constrain its placement.
	 * @param slv The given Solver.
	 */
	@SuppressWarnings("unchecked")
	private void createBigRoomConstraints(Solver slv){
		
		// Throne room
		rooms.get(0).setWidth((int) (0.4 * CANVAS_WIDTH));
		rooms.get(0).setHeight((int) (0.6 * CANVAS_WIDTH * SCALE_FACTOR));
		
		slv.add(ctx.mkAnd(
			ctx.mkGe(rooms.get(0).getX(), ctx.mkReal(3 * CANVAS_WIDTH, 10)),
			ctx.mkLe(rooms.get(0).getX(), ctx.mkReal(35 * CANVAS_WIDTH, 100)),
			ctx.mkGe(rooms.get(0).getY(), ctx.mkReal(CANVAS_HEIGHT * SCALE_FACTOR, 10)),
			ctx.mkLe(rooms.get(0).getY(), ctx.mkReal(CANVAS_HEIGHT * SCALE_FACTOR, 4))
		));

		andClauseCount += 4;

		// Antechamber
		rooms.get(1).setWidth((int) (0.4 * CANVAS_WIDTH));
		rooms.get(1).setHeight((int) (0.05 * CANVAS_WIDTH * SCALE_FACTOR));
		rooms.get(2).setWidth(15);
		rooms.get(2).setWidth(15 * SCALE_FACTOR);
	}

	/**
	 * Add constraints to the given Solver that determine the separation between rooms.
	 * @param slv The given Solver.
	 */
	private void createSeparationContraints(Solver slv){
		for(int i = 0; i < numberOfRooms; i++){
			for(int j = i + 1; j < numberOfRooms; j++){
				if(bigRoomConstraint){
					if(i == 0 && (j == 1 || j == 2)){
						addBigRoomSeparationConstraint(slv, i, j);
					}
					else{
						addSeparationConstraint(slv, i, j);
					}
				}
				else{
					addSeparationConstraint(slv, i, j);
				}
			}
		}
	}
	
	/**
	 * Add constraints to the given Solver for antechamber and escape room dimensions and placement.
	 * @param slv The given Solver.
	 * @param i The index of the throne room.
	 * @param j The index of the antechamber or exit room.
	 */
	@SuppressWarnings("unchecked")
	private void addBigRoomSeparationConstraint(Solver slv, int i, int j)
	{
		// Have antechamber touching throne room bottom
		if(j == 1)
		{
			slv.add(ctx.mkAnd(
				ctx.mkEq(rooms.get(i).getY(), ctx.mkSub(rooms.get(j).getY(), ctx.mkInt(rooms.get(i).getHeight()))),
				ctx.mkEq(rooms.get(i).getX(), rooms.get(j).getX())
			));
			andClauseCount += 2;
		}
		// Have escape room touching top right of throne room
		if(j == 2)
		{	
			slv.add(ctx.mkAnd(
				ctx.mkEq(rooms.get(i).getX(), ctx.mkSub(rooms.get(j).getX(), ctx.mkInt(rooms.get(i).getWidth()))),
				ctx.mkEq(rooms.get(i).getY(), ctx.mkSub(rooms.get(j).getY(), ctx.mkReal(rooms.get(i).getHeight(), 10)))
			));
			andClauseCount += 2;
		}
	}
	
	/**
	 * Adds constraints to the given Solver to ensure rooms are separated by a certain number of units.
	 * @param slv The given Solver.
	 * @param i The index of the first room.
	 * @param j The index of the second room.
	 */
	@SuppressWarnings("unchecked")
	private void addSeparationConstraint(Solver slv, int i, int j)
	{
		slv.add(ctx.mkOr(
			ctx.mkLe(rooms.get(j).getY(), ctx.mkSub(rooms.get(i).getY(), ctx.mkInt(rooms.get(j).getHeight() + SEPARATION_Y))),
			ctx.mkLe(rooms.get(i).getY(), ctx.mkSub(rooms.get(j).getY(), ctx.mkInt(rooms.get(i).getHeight() + SEPARATION_Y))),
			ctx.mkLe(rooms.get(j).getX(), ctx.mkSub(rooms.get(i).getX(), ctx.mkInt(rooms.get(j).getWidth() + SEPARATION))),
			ctx.mkLe(rooms.get(i).getX(), ctx.mkSub(rooms.get(j).getX(), ctx.mkInt(rooms.get(i).getWidth() + SEPARATION)))
		));
		andClauseCount++;
		orClauseCount += 4;
	}

	/**
	 * Adds constraints to the given Solver to ensure rooms are placed within the playfield.
	 * @param slv The given Solver.
	 */
	@SuppressWarnings("unchecked")
	private void createCanvasConstraints(Solver slv){
		for(int i = 0; i < numberOfRooms; i++){
			slv.add(
				ctx.mkGe(rooms.get(i).getX(), ctx.mkInt(0)),
				ctx.mkLe(ctx.mkAdd(rooms.get(i).getX(), ctx.mkInt(rooms.get(i).getWidth())), ctx.mkInt(CANVAS_WIDTH))
			);
			slv.add(
				ctx.mkGe(rooms.get(i).getY(), ctx.mkInt(0)),
				ctx.mkLe(ctx.mkAdd(rooms.get(i).getY(), ctx.mkInt(rooms.get(i).getHeight())), ctx.mkInt(CANVAS_HEIGHT * SCALE_FACTOR))
			);
			andClauseCount += 4;
		}
	}

	/**
	 * Adds constraints to the given Solver to restrict room placement within the bounds of linear functions.
	 * @param slv The given Solver.
	 */
	@SuppressWarnings("unchecked")
	private void createLineConstraints(Solver slv){
		for(int i = 0; i < numberOfRooms; i++){
			// X shape
			slv.add(ctx.mkOr(
				ctx.mkAnd(
					ctx.mkGe(ctx.mkAdd(rooms.get(i).getY(), rooms.get(i).getX()), ctx.mkInt(380 - LINEWIDTH)),
					ctx.mkLe(ctx.mkAdd(rooms.get(i).getY(), rooms.get(i).getX()), ctx.mkInt(380 + LINEWIDTH))
				),
				ctx.mkAnd(
					ctx.mkGe(rooms.get(i).getX(), ctx.mkSub(rooms.get(i).getY(), ctx.mkInt(LINEWIDTH))),
					ctx.mkLe(rooms.get(i).getX(), ctx.mkAdd(rooms.get(i).getY(), ctx.mkInt(LINEWIDTH)))
				)
			));
			andClauseCount += 4;
			orClauseCount += 2;
		}
	}

	/**
	 * Adds constraints to the given Solver to guide room placement along the given control lines.
	 * @param slv The given Solver.
	 * @param lines The given control lines.
	 */
	private void createPointLineConstraints(Solver slv, ArrayList<HashMap<String, Double>> lines){
		String constraint = "";
		for(int i = 0; i < numberOfRooms; i++){
			if(bigRoomConstraint && (i == 0 || i == 1 || i ==2)){
				continue;
			}
			double high_y, low_y, high_x, low_x;
			constraint = "Or(";
			for(HashMap<String, Double> line: lines){
				if(line.get("m") > 0){
					constraint += "And((rooms[i]['y'] <= " + Double.toString(line.get("m")) + "* (rooms[i]['x'] - "
                               + Double.toString(line.get("x2")) + "+" + Integer.toString(LINEWIDTH) + ") +" + Double.toString(line.get("y2")) + "),\n";
                	constraint += "(rooms[i]['y'] >= " + Double.toString(line.get("m")) + "* (rooms[i]['x'] - "
                               + Double.toString(line.get("x2")) + "-" + Integer.toString(LINEWIDTH) + "+" + Integer.toString(rooms.get(i).getWidth()) + ")+" + Double.toString(line.get("y2")) + "),\n";
				}
				else{
					constraint += "And((rooms[i]['y'] >= " + Double.toString(line.get("m")) + "* (rooms[i]['x'] - "
                               + Double.toString(line.get("x2")) + "+" + Integer.toString(LINEWIDTH) + ") +" + Double.toString(line.get("y2")) + "),\n";
                	constraint += "(rooms[i]['y'] <= " + Double.toString(line.get("m")) + "* (rooms[i]['x'] - "
                               + Double.toString(line.get("x2")) + "-" + Integer.toString(LINEWIDTH) + "+" + Integer.toString(rooms.get(i).getWidth()) + ")+" + Double.toString(line.get("y2")) + "),\n";
				}

				if(line.get("y2") > line.get("y1")){
					high_y = line.get("y2");
					low_y = line.get("y1");
				}
				else{
					high_y = line.get("y1");
					low_y = line.get("y2");
				}

				if(high_y - rooms.get(i).getHeight() > low_y){
					constraint += "(rooms[i]['y'] >= " + Double.toString(low_y) + "),\n";
                	constraint += "(rooms[i]['y'] <= " + Double.toString(high_y) + "-" + Integer.toString(rooms.get(i).getHeight()) + ")),\n";
				}
				else{
					if(line.get("x2") > line.get("x1")){
						high_x = line.get("x2");
						low_x = line.get("x1");
					}
					else{
						high_x = line.get("x1");
						low_x = line.get("x2");
					}
					constraint += "(rooms[i]['x'] >= " + Double.toString(low_x) + "),\n";
					constraint += "(rooms[i]['x'] <= " + Double.toString(high_x) + "-" + Integer.toString(rooms.get(i).getWidth()) + ")),\n";
				}
				andClauseCount = andClauseCount + 4;
				orClauseCount = orClauseCount + 1;
			}
			constraint = constraint.substring(0, constraint.length() - 2);
			constraint += "\n";
			System.out.println("Room: " + Integer.toString(i) + "  Constraint: \n" + constraint + "\n\n");
			slv.add(eval(constraint));
		}
	}

	/**
	 * Add a series of linear constraints following lines created by mousepoints.
	 * @param slv The given Solver.
	 * @param mousepoints The list of mousepoints.
	 */
	private void createMousepointConstraints(Solver slv, ArrayList<Double> mousepoints){
		ArrayList<HashMap<String, Double>> lines = new ArrayList<HashMap<String, Double>>();
		HashMap<String, Double> l_info = new HashMap<String, Double>();
		double x1, y1, x2, y2, m_num, m_den;
		double prev_x, prev_y, p_x, p_y;
		for(int i = 0; i < mousepoints.size(); i += 2){
			p_x = mousepoints.get(i);
			p_y = mousepoints.get(i + 1);
			if(prev_x == 0 && prev_y == 0){
				prev_x = p_x;
				prev_y = p_y;
				continue;
			}
			x1 = (prev_x - BORDER);
			y1 = (prev_y - BORDER) * SCALE_FACTOR;
			x2 = (p_x - BORDER);
			y2 = (p_y - BORDER) * SCALE_FACTOR;
			m_num = (y2 - y1);
			if((x2 - x1) == 0){
				m_den = 1;
			}
			else{
				m_den = (x2 - x1);
			}
			l_info.put("m_num", m_num);
			l_info.put("m_den", m_den);
			l_info.put("m", m_num/m_den);
			l_info.put("y1", y1);
			l_info.put("y2", y2);
			l_info.put("x1", x1);
			l_info.put("x2", x2);
			System.out.print("slope: " + Double.toString(m_num/m_den));
			System.out.print("  slope_num: " + Double.toString(m_num));
			System.out.print("  slope_den: " + Double.toString(m_den));
			System.out.print("  x2: " + Double.toString(x2));
			System.out.println("  y2: " + Double.toString(y2));
			lines.add(l_info);
			prev_x = p_x;
			prev_y = p_y;
		}
		createPointLineConstraints(slv, lines);
	}

	/**
	 * Adds constraints to the given Solver to restrict room placement to specific quadrants of the playfield.
	 * @param slv The given Solver.
	 */
	@SuppressWarnings("unchecked")
	private void createQuadConstraints(Solver slv){
		for(int i = 0; i < numberOfRooms; i++){
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
			andClauseCount += 2;
		}
	}
	
	/**
	 * Initializes all constraints and adds them to the given Solver.
	 * @param slv The given Solver.
	 * @param mousepoints Coordinates for the points of control lines.
	 */
	private void initAllConstraints(Solver slv, ArrayList<Double> mousepoints)
	{
		long begin, all_begin, end, all_end;
		andClauseCount = 0;
		orClauseCount = 0;
		begin = System.currentTimeMillis();
		all_begin = begin;
		createCanvasConstraints(slv);
		end = System.currentTimeMillis();
		timingInfo.put("createCanvasConstraints", (end - begin) / 1000.0);
		
		if(bigRoomConstraint)
		{
			begin = System.currentTimeMillis();
			createBigRoomConstraints(slv);
			end = System.currentTimeMillis();
			timingInfo.put("createBigRoomConstraints", (end - begin) / 1000.0);
		}
		begin = System.currentTimeMillis();
		createSeparationContraints(slv);
		end = System.currentTimeMillis();
		timingInfo.put("createSeparationConstraints", (end - begin) / 1000.0);
		
		if(lineConstraints)
		{
			begin = System.currentTimeMillis();
			createLineConstraints(slv);
			end = System.currentTimeMillis();
			timingInfo.put("createLineConstraints", (end - begin) / 1000.0);
		}
		
		if(quadConstraints)
		{
			begin = System.currentTimeMillis();
			createQuadConstraints(slv);
			end = System.currentTimeMillis();
			timingInfo.put("createQuadConstraints", (end - begin) / 1000.0);
		}
		
		if(mousepoints.size() >= 2)
		{
			begin = System.currentTimeMillis();
			createMousepointConstraints(slv, mousepoints);
			end = System.currentTimeMillis();
			timingInfo.put("createControlLineConstraints", (end - begin) / 1000.0);
		}
		
		all_end = System.currentTimeMillis();
		timingInfo.put("createAllConstraints", (all_end - all_begin) / 1000.0);
		System.out.println("======");
		System.out.println("And clause count: " + andClauseCount);
		System.out.println("Or clause count: " + orClauseCount);
	}

	/**
	 * Displays the information of all rooms.
	 */
	private void displayRoomInfo()
	{
		for(int i = 0; i < numberOfRooms; i++){
			System.out.println("Room " + Integer.toString(i) + ":: width: " + Integer.toString(rooms.get(i).getWidth()) 
			+ "  height: " + Integer.toString(rooms.get(i).getHeight()));
		}
	}
	
	/**
	 * Generates rooms based on the interpreted room constraints in the given model. Also displays
	 * Delaunay triangulation and minimum spanning tree if desired.
	 * @param m The given Model.
	 * @param surf The Node in which the rooms will be displayed.
	 * @param tri Delaunay triangulation for room layout.
	 * @param mst Minimum spanning tree for room layout.
	 * @param centerpoints Array of room centerpoints.
	 * @param mousepoints Array of point coordinates of control lines.
	 */
	private void drawRooms(Model m, Group surf, DelaunayTriangulator tri, int[][] mst, float[][] centerpoints, ArrayList<Double> mousepoints)
	{
		Rectangle rectangle;
		for(int i = 0; i < numberOfRooms; i++)
		{
			rectangle = new Rectangle(
				(valueOf(m, rooms.get(i).getX()) + BORDER),
				((valueOf(m, rooms.get(i).getY()) / SCALE_FACTOR) + BORDER),
				rooms.get(i).getWidth(),
				(rooms.get(i).getHeight() / SCALE_FACTOR)
			);
			rectangle.setFill(null);
			rectangle.setStrokeWidth(2);
			
			switch(rooms.get(i).getQuad())
			{
			case 1:
				rectangle.setStroke(Color.BLACK);
				break;
			case 2:
				rectangle.setStroke(Color.rgb(255, 133, 27));	// orange
				break;
			case 3:
				rectangle.setStroke(Color.rgb(0, 116, 217));	// blue
				break;
			case 4:
				rectangle.setStroke(Color.rgb(46, 204, 64));	// green
				break;
			default:
				break;
			}// end switch
			
			surf.getChildren().add(rectangle);
			// TODO remove in final product
			Label label = new Label(i + "");
			label.setLayoutX(rooms.get(i).getCenterX());
			label.setLayoutY(valueOf(m, rooms.get(i).getY()) / SCALE_FACTOR);
			surf.getChildren().add(label);
			
		}// end for
		
		if(!tri.getTriangles().isEmpty())
		{
			// Draw Delaunay triangulation
			if(showDelaunay)
			{
				Polyline lines;
				
				for(Triangle2D triangle : tri.getTriangles())
				{
					// vertical scaling is done when centerpoints are computed
					lines = new Polyline(
						(triangle.a.x + BORDER), (triangle.a.y/* / SCALE_FACTOR*/) + BORDER,
						(triangle.b.x + BORDER), (triangle.b.y/* / SCALE_FACTOR*/) + BORDER,
						(triangle.c.x + BORDER), (triangle.c.y/* / SCALE_FACTOR*/) + BORDER,
						(triangle.a.x + BORDER), (triangle.a.y/* / SCALE_FACTOR*/) + BORDER
					);
					lines.setStroke(Color.rgb(0, 45, 225));	// dark blue
					
					surf.getChildren().add(lines);
				}
			}
			
		}// end if
		
		if(mst.length > 1)
		{
			if(showSparse)
			{
				Line line;
				
				// vertical scaling is done when centerpoints are computed
				for(int[] points : mst)
				{
					line = new Line(
						(double) centerpoints[points[0]][0] + BORDER,
						(double) (centerpoints[points[0]][1]/* / SCALE_FACTOR*/) + BORDER,
						(double) centerpoints[points[1]][0] + BORDER,
						(double) (centerpoints[points[1]][1]/* / SCALE_FACTOR*/) + BORDER
					);
					line.setStroke(Color.rgb(0, 225, 0));	// lime green
					
					surf.getChildren().add(line);
				}
			}
		}
		
		// TODO may not need this code
		if(!mousepoints.isEmpty())
		{
			Polyline lines = new Polyline();
			lines.setStroke(Color.rgb(139, 0, 0));	// dark red
			lines.getPoints().addAll(mousepoints);
			surf.getChildren().add(lines);
		}
		
		drawPassageways(m, surf, mst);
		
	}// end drawRooms
	
	/**
	 * Computes the distance between the two given points.
	 * @param point1 Float array in the form [x1, y1].
	 * @param point2 Float array in the form [x2, y2].
	 * @return The distance between the two given points
	 */
	private double distance(float[] point1, float[] point2)
	{// TODO may not need this method
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
		// vertical scaling is done when centerpoints are computed
		return Math.sqrt(Math.pow((point2.x - point1.x), 2) + Math.pow((point2.y - point1.y)/* / SCALE_FACTOR*/, 2));
	}
	
	/**
	 * Creates 2D array (matrix) representing the given triangulation.
	 * @param tri The given triangulation.
	 * @param cp The set of points in the triangulation. TODO consider removing this argument.
	 * @param edges The set of edges in the triangulation.
	 * @return The matrix containing distances between points (rows/columns) in the given triangulation. TODO may only need to return edges
	 */
	private double[][] createGraphArray(DelaunayTriangulator tri, float[][] cp, ArrayList<Edge> edges)
	{
		double[][] graph = new double[numberOfRooms][numberOfRooms];
		
		for(Triangle2D t : tri.getTriangles())
		{
			// Prevent duplicate edges/distances
			if(true)//.a.index < t.b.index)
			{
//				graph[t.a.index][t.b.index] = distance(cp[t.a.index], cp[t.b.index]);
				graph[t.a.index][t.b.index] = distance(t.a, t.b);
				edges.add(new Edge(t.a.index, t.b.index, graph[t.a.index][t.b.index]));
			}
			
			// Prevent duplicate edges/distances
			if(true)//.b.index < t.c.index)
			{
//				graph[t.b.index][t.c.index] = distance(cp[t.b.index], cp[t.c.index]);
				graph[t.b.index][t.c.index] = distance(t.b, t.c);
				edges.add(new Edge(t.b.index, t.c.index, graph[t.b.index][t.c.index]));
			}
			
			// Prevent duplicate edges/distances
			if(true)//.c.index < t.a.index)
			{
//				graph[t.c.index][t.a.index] = distance(cp[t.c.index], cp[t.a.index]);
				graph[t.c.index][t.a.index] = distance(t.c, t.a);
				edges.add(new Edge(t.c.index, t.a.index, graph[t.c.index][t.a.index]));
			}
			
		}// end for
		
		// TODO remove after program works
//		for(float[] a : cp)
//		{
//			for(float f : a)
//			{
//				System.out.print(" " + f);
//			}
//			System.out.println();
//		}
		for(double[] a : graph)
		{
			for(double d : a)
			{
				System.out.print(" " + d);
			}
			System.out.println();
		}
		
		return graph;
		
	}// end createGraphArray
	
	/**
	 * Provides the set of integers that the two given ranges share.
	 * @param range1 The first range.
	 * @param range2 The second range.
	 * @return The set of integers that the two given ranges share.
	 */
	private int[] overlap(int[] range1, int[] range2)
	{
		if(!rangeOverlapping(range1, range2))
		{
			return new int[] {};
			
		} else {
			
			return IntStream.rangeClosed(Math.max(range1[0], range2[0]), Math.min(range1[1], range2[1])).toArray();
		}
	}
	
	/**
	 * Determines whether the two given ranges of integers overlap.
	 * @param range1 The first range.
	 * @param range2 The second range.
	 * @return True if the ranges overlap, false otherwise.
	 */
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
	
	/**
	 * Draws passageways between rooms of the given model based on the minimum spanning tree of their layout.
	 * @param m The given model.
	 * @param surf The Node in which the passageways will be displayed.
	 * @param mst Minimum spanning tree for room layout.
	 */
	private void drawPassageways(Model m, Group surf, int[][] mst)
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
		{// TODO check if mst is formatted properly
			// Determine which room is above the other room
			if(valueOf(m, rooms.get(points[0]).getY()) < valueOf(m, rooms.get(points[1]).getY()))
			{
				top = points[0];
				bottom = points[1];
				
			} else {
				
				top = points[1];
				bottom = points[0];
			}
			
			// Determine which room is to right of other room
			if(valueOf(m, rooms.get(points[0]).getX()) < valueOf(m, rooms.get(points[1]).getX()))
			{
				left = points[0];
				right = points[1];
				
			} else {
				
				right = points[0];
				left = points[1];
			}
			
			int[] top_x_range = new int[] {valueOf(m, rooms.get(top).getX()) + PASSAGE_WIDTH, valueOf(m, rooms.get(top).getX()) + rooms.get(top).getWidth() - PASSAGE_WIDTH};
			int[] top_y_range = new int[] {valueOf(m, rooms.get(top).getY()) + PASSAGE_WIDTH, valueOf(m, rooms.get(top).getY()) + rooms.get(top).getHeight() - PASSAGE_WIDTH};
			int[] bottom_x_range = new int[] {valueOf(m, rooms.get(bottom).getX()) + PASSAGE_WIDTH, valueOf(m, rooms.get(bottom).getX()) + rooms.get(bottom).getWidth() - PASSAGE_WIDTH};
			int[] bottom_y_range = new int[] {valueOf(m, rooms.get(bottom).getY()) + PASSAGE_WIDTH, valueOf(m, rooms.get(bottom).getY()) + rooms.get(bottom).getHeight() - PASSAGE_WIDTH};
			
			Polyline lines = new Polyline();
			lines.setStrokeWidth(PASSAGE_WIDTH);
			lines.setStroke(Color.ORANGE); // TODO remove after full implementation
			
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
						(double) passX + BORDER, (((valueOf(m, rooms.get(top).getY()) + rooms.get(top).getHeight()) / (double) SCALE_FACTOR) + BORDER),
						(double) passX + BORDER, ((valueOf(m, rooms.get(bottom).getY()) / (double) SCALE_FACTOR) + BORDER)
					);
					
					surf.getChildren().add(lines);
				}
				
			} else {
				
				if(rangeOverlapping(top_y_range, bottom_y_range))
				{
					// y overlap, no x overlap, draw line straight across
					overlap = overlap(top_y_range, bottom_y_range);
					passY = overlap[random.nextInt(overlap.length)];
					lines.getPoints().addAll(
						(double) (valueOf(m, rooms.get(left).getX()) + rooms.get(left).getWidth() + BORDER), ((passY / (double) SCALE_FACTOR) + BORDER),
						(double) (valueOf(m, rooms.get(right).getX()) + BORDER), ((passY / (double) SCALE_FACTOR) + BORDER)
					);
					
					surf.getChildren().add(lines);
					
				} else {
					
					// no x overlap, no y overlap, draw right-angle connector
					passX = random.nextInt(bottom_x_range[1] - bottom_x_range[0]) + bottom_x_range[0];
					passY = random.nextInt(top_y_range[1] - top_y_range[0]) + top_y_range[0];
					if(top == left)
					{
						lines.getPoints().addAll(
							(double) (valueOf(m, rooms.get(top).getX()) + rooms.get(top).getWidth() + BORDER), ((passY / (double) SCALE_FACTOR) + BORDER)
						);
						
					} else {
						
						lines.getPoints().addAll(
							(double) (valueOf(m, rooms.get(top).getX()) + BORDER),
							((passY / (double) SCALE_FACTOR) + BORDER)
						);
					}
					
					lines.getPoints().addAll(
						(passX + BORDER + ((double) PASSAGE_WIDTH / 2)), ((passY / (double) SCALE_FACTOR) + BORDER)
					);
					
					surf.getChildren().add(lines);
					
					lines = new Polyline();
					lines.setStrokeWidth(PASSAGE_WIDTH);
					lines.setStroke(Color.ORANGE); // TODO remove after full implementation
					lines.getPoints().addAll(
						(double) (passX + BORDER), ((passY / (double) SCALE_FACTOR) + BORDER),
						(double) (passX + BORDER), ((valueOf(m, rooms.get(bottom).getY()) / (double) SCALE_FACTOR) + BORDER)
					);
					
					surf.getChildren().add(lines);
					
				}// end if
				
			}// end if
			
		}// end for
		
	}// end drawPassageways
	
	/**
	 * Initialize the grid used for computing rectangle placement density.
	 */
	private void initGridCounts()
	{
		gridCounts = new int[CANVAS_HEIGHT / GRID_CELL][CANVAS_WIDTH / GRID_CELL];
	}
	
	/**
	 * Update the grid counts based on the current set of rooms.
	 * @param m The Model containing the current set of rooms.
	 */
	private void updateGrid(Model m)
	{
		for(int i = 0; i < numberOfRooms; i++)
		{
			updateGridCounts(m, rooms.get(i));
		}
	}
	
	/**
	 * Update grid counts based on which cells the passed room overlaps.
	 * @param m The given Model.
	 * @param r The given Room.
	 */
	private void updateGridCounts(Model m, Room r)
	{
		int rX = valueOf(m, r.getX());
		int rY = valueOf(m, r.getY());
		
		int startGridX = rX / GRID_CELL;
		int endGridX = (rX + r.getWidth()) / GRID_CELL;
		
		int startGridY = rY / GRID_CELL_Y;
		int endGridY = (rY + r.getHeight()) / GRID_CELL_Y;
		
		for(int i = startGridY; i < endGridY; i++)
		{
			for(int j = startGridX; j < endGridX; j++)
			{
				gridCounts[i][j] += 1;
			}
		}
	}
	
	private void makeHeatmap()
	{
		DefaultHeatMapDataset dataset = new DefaultHeatMapDataset(CANVAS_WIDTH / GRID_CELL, CANVAS_HEIGHT / GRID_CELL, 0,CANVAS_WIDTH / GRID_CELL, 0, CANVAS_HEIGHT / GRID_CELL);
		for(int i = 0; i < gridCounts.length; i++)
		{
			for(int j = 0; j < gridCounts[i].length; j++)
			{
				// TODO may need to swap i and j
				dataset.setZValue(i, j, gridCounts[i][j] / NUM_RUNS);
			}
		}
		try
		{
			File file = new File("{}x{}_{}_{}_{}_{}_{}_{}rooms_{}runs");
			ImageIO.write(HeatMapUtils.createHeatMapImage(dataset, new GrayPaintScale()), "jpg", file);
			
		} catch(IOException e) {
			
			e.printStackTrace();
		}
	}
	
	private void resetAccumulatedTiming(){
		for(String timing: accumulatedTimingInfo.keySet()){
			accumulatedTimingInfo.put(timing, new ArrayList<Long>());
		}
	}

	private void updateTiming()
	{
		if(accumulatedTimingInfo == null){
			System.out.println("Initializing accumulatedTimingInfo");
			for(String timing: timingInfo.keySet()){
				accumulatedTimingInfo.put(timing, new ArrayList<Long>());
			}
		}

		for(String timing: timingInfo.keySet()){
			accumulatedTimingInfo.get(timing).add(timingInfo.get(timing));
		}
	}
	
	private void doHistogram(ArrayList<Long> timings, String timing)
	{
		File file = new File("{}_hist_{}x{}_{}_{}_{}_{}_{}_{}rooms_{}runs.svg");
		try
		{
			SVGGraphics2D g2 = new SVGGraphics2D(600, 400);
			DefaultIntervalXYDataset dataset = new DefaultIntervalXYDataset();
			ChartFactory.createHistogram(null, null, null, dataset).draw(g2, new java.awt.Rectangle(0, 0, 600, 400));;
			SVGUtils.writeToSVG(file, g2.getSVGElement());
			
		} catch(IOException e) {
			
			e.printStackTrace();
		}
	}
	
	private void finalDataAnalysis()
	{
		HashMap<String, Long> finalAnalysis = new HashMap<String, Long>();
		String filename, quadConstraint;
		for(String timing: accumulatedTimingInfo.keySet()){
			ArrayList<Long> timings = accumulatedTimingInfo.get(timing);
			ArrayList<Long> timingsCopy = new ArrayList<Long>();
			long upper, lower;
			long avg, med, max, sum;
			long min = timings.get(0);
			for(Long time: timings){
				timingsCopy.add(time);
				sum += time;
				if(time > max){
					max = time;
				}
				else if(time < min){
					min = time;
				}
			}
			avg = sum / timings.size();
			Collections.sort(timingsCopy);
			if(timingsCopy.size() % 2 == 1){
				med = timingsCopy.get((timingsCopy.size() + 1) / 2 - 1);
			}
			else{
				lower = timingsCopy.get(timingsCopy.size() / 2 - 1);
				upper = timingsCopy.get(timingsCopy.size() / 2);
				med = (lower + upper) / 2;
			}

			finalAnalysis.put(timing + "_average", avg);
			System.out.println(timing + " average " + Long.toString(avg));
			finalAnalysis.put(timing + "_median", med);
			System.out.println(timing + " median " + Long.toString(med));
			finalAnalysis.put(timing + "_minimum", min);
			System.out.println(timing + " minimum " + Long.toString(min));
			finalAnalysis.put(timing + "_maximum", max);
			System.out.println(timing + " maximum " + Long.toString(max));

			doHistogram(accumulatedTimingInfo.get(timing), timing);

			if(quadConstraints){
				quadConstraint = "quads";
			}
			else{
				quadConstraint = "noquads";
			}
			
			filename = "Alldata_hist_" + Integer.toString(CANVAS_WIDTH) + "x" +
			Integer.toString(CANVAS_HEIGHT) + "_" + Integer.toString(ROOM_WIDTH_MIN) + "_" +
			Integer.toString(ROOM_WIDTH_MAX) + "_" + Integer.toString(ROOM_HEIGHT_MIN) + "_" +
			Integer.toString(ROOM_HEIGHT_MAX) + "_" + quadConstraint + "_" + Integer.toString(numberOfRooms) +
			"rooms_" + Integer.toString(NUM_RUNS) + "runs.json";
			
			try{
				FileWriter file = new FileWriter(new File(filename));
				for(String t: accumulatedTimingInfo.keySet()){
					file.write(t + "\n");
					file.write(accumulatedTimingInfo.get(t) + "\n");
				}
				file.close();
			}
			catch(IOException e){
				e.printStackTrace();
			}
		}
	}
	
	private void saveMousepointData(ArrayList<Double> mp)
	{
		try{
			FileWriter file = new FileWriter(new File("mousepoints.json"));
			for(double p: mp){
				file.write(p + "\n");
			}
			file.close();
		}
		catch(IOException e){
			e.printStackTrace();
		}
		System.out.println("Wrote mousepoints to disk, file: mousepoints.json");
	}
	
	private ArrayList<Double> loadMousepointData()
	{
		ArrayList<Double> mp = new ArrayList<Double>();
		try {
			File obj = new File("mousepoints.json");
			Scanner reader = new Scanner(obj);
			while(reader.hasNextLine()) {
			  String data = reader.nextLine();
			  mp.add(Double.parseDouble(data));
			}
			reader.close();
		  } catch (FileNotFoundException e) {
			e.printStackTrace();
		  }
		  System.out.println("Read mousepoints from disk, file: mousepoints.json");
		  return mp;
	}
	
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
			
			// Remove the vertex if it does not have any unique adjacencies
			if(uniqueAdjacencies.get(currentVertex.getIndex()).size() < 1)
			{
				uniqueAdjacencies.remove(currentVertex.getIndex());
			}
		}
		
		ArrayList<int[]> pairList = new ArrayList<>(adjacencyCount);
		int[][] pairArray = new int[adjacencyCount][2];
		
		// Group all adjacencies into pairs
		for(Map.Entry<Integer, ArrayList<Integer>> adjacencies : uniqueAdjacencies.entrySet())
		{
			for(int adjacentVertex = 0; adjacentVertex < adjacencies.getValue().size(); adjacentVertex++)
			{
				pairList.add(new int[] {adjacencies.getKey(), adjacencies.getValue().get(adjacentVertex)});
			}
		}
		
		pairList.toArray(pairArray);
		
		// TODO remove after program works
		for(Vertex v1 : vertices)
		{
			System.out.print(v1.getIndex() + ": ");
			for(Vertex v2 : v1.getAdjacencies())
			{
				System.out.print(v2.getIndex() + ", ");
			}
			System.out.println();
		}
		for(int[] a : pairArray)
		{
			for(int i : a)
			{
				System.out.print(" " + i);
			}
			System.out.println();
		}
		
		return pairArray;
		
	}// end getMst
	
	/**
	 * Converts the interpretation of the given integer expression into an Integer object.
	 * @param m The model for which the given integer expression has an interpretation.
	 * @param e The given integer expression.
	 * @return The interpretation of the given integer expression as an Integer object.
	 */
	private Integer valueOf(Model m, IntExpr e)
	{
		return Integer.parseInt(m.getConstInterp(e).toString());
	}
	
	@Override
	public void start(Stage primaryStage)
	{
		// TODO may not need this data structure (could use Polyline object instead?)
		ArrayList<Double> mousepoints = new ArrayList<>();	// data structure containing points for control lines specified by the user
		
		Polyline controlLines = new Polyline();
		Pane pane = new Pane(controlLines); // displays the dungeon layout and contains control lines
		
		// control for specifying the number of rooms in the dungeon
		Spinner<Integer> roomSpinner = new Spinner<>(5, 30, NUM_ROOMS);
		roomSpinner.setEditable(true);
		roomSpinner.setMaxWidth(60);
		
		// control for specifying the number times to run the solver
		Spinner<Integer> runSpinner = new Spinner<>(1, 25, NUM_RUNS);
		runSpinner.setEditable(true);
		runSpinner.setMaxWidth(60);
		
		// control for specifying the number iterations to perform during each run
		Spinner<Integer> iterationSpinner = new Spinner<>(1, 100, NUM_LOOPS);
		iterationSpinner.setEditable(true);
		iterationSpinner.setMaxWidth(60);
		
		Button start = new Button("Start"); // starts the solver
		Button stop = new Button("Stop"); // stops the solver
		stop.setDisable(true);
		
		HBox upperControls = new HBox
		(
			new VBox(new Label("Number of rooms"), roomSpinner),
			new VBox(new Label("Number of runs"), runSpinner),
			new VBox(new Label("Iterations per run"), iterationSpinner),
			new VBox(start, stop)
		);
		upperControls.setAlignment(Pos.CENTER);
		upperControls.setSpacing(10);
		
		// Constraint controls
		RadioButton toggleLineConstraints = new RadioButton("Lines");
		toggleLineConstraints.setOnAction(e ->
		{
			lineConstraints = !lineConstraints;
		});
		RadioButton toggleQuadConstraints = new RadioButton("Quadrants");
		toggleQuadConstraints.setOnAction(e ->
		{
			quadConstraints = !quadConstraints;
		});
		RadioButton toggleBigRoomConstraint = new RadioButton("Big Room");
		toggleBigRoomConstraint.setOnAction(e ->
		{
			bigRoomConstraint = !bigRoomConstraint;
		});
		
		// Layout controls
		RadioButton toggleDelaunay = new RadioButton("Delaunay");
		toggleDelaunay.setOnAction(e ->
		{
			showDelaunay = !showDelaunay;
		});
		RadioButton toggleSparse = new RadioButton("Sparse");
		toggleSparse.setOnAction(e ->
		{
			showSparse = !showSparse;
		});
		
		// Mousepoint controls
		Button saveMousepoints = new Button("Save");
		saveMousepoints.setOnAction(e ->
		{
			saveMousepointData(mousepoints);
		});
		Button loadMousepoints = new Button("Load");
		loadMousepoints.setOnAction(e ->
		{
//			mousepoints = loadMousepointData();
			FileChooser fileChooser = new FileChooser();
			//fileChooser.setInitialDirectory(new File(PATH));
			File selectedFile = fileChooser.showOpenDialog(new Stage());
		});
		VBox mousepointControls = new VBox(
			new Label("Mousepoints"),
			new HBox(saveMousepoints, loadMousepoints)
		);
		
		Button clearPane = new Button("Clear");
		clearPane.setOnAction(e ->
		{
			mousepoints.clear();
			controlLines.getPoints().clear();
			pane.getChildren().retainAll(controlLines);
		});
		
		HBox lowerControls = new HBox(
			new VBox(new Label("Constraints"), toggleLineConstraints, toggleQuadConstraints, toggleBigRoomConstraint),
			new VBox(new Label("Display"), toggleDelaunay, toggleSparse),
			mousepointControls,
			clearPane
		);
		lowerControls.setSpacing(5);
		lowerControls.setAlignment(Pos.CENTER);
		
		VBox uiControls = new VBox(upperControls, lowerControls);
		
		BorderPane borderPane = new BorderPane();
		borderPane.setTop(uiControls);
		borderPane.setCenter(pane);
		
		Button testButton = new Button("Test");
		testButton.setOnAction(event ->
		{
			ctx = new Context();
			solver = ctx.mkSolver();
			System.out.println((solver.check() == Status.SATISFIABLE));
		});
		//pane.getChildren().add(testButton);
		Scene scene = new Scene(borderPane, CANVAS_WIDTH + 2*BORDER, CANVAS_HEIGHT + 2*BORDER + 118/*height of uiControls*/);
		primaryStage.setScene(scene);
		primaryStage.setTitle("Dungeon Generator");
		primaryStage.show();
		
		primaryStage.setOnCloseRequest(e ->
		{
			loopCount = 0;
			runCount = 0;
			if(solver != null)
			{
				try
				{
					solver.interrupt();
					
				} catch(Z3Exception z) {}
			}
			ctx.close();
		});
		
		// if the mouse is being used to create points, use the points for control lines
		pane.setOnMouseClicked(event ->
		{
			if(event.getButton() == MouseButton.PRIMARY)
			{
				mousepoints.add(event.getX());
				mousepoints.add(event.getY());
				System.out.println("Added: " + event.getX() + ", " + event.getY());
				controlLines.getPoints().add(event.getX());
				controlLines.getPoints().add(event.getY());
			}
		});
		
		System.out.println("Dungeon layout using SMT");
		initGridCounts(); // counts the number of grid cells within the play area
		ctx = new Context();
		
		start.setOnAction(e ->
		{
			// disable all controls and enable stop button
			roomSpinner.setDisable(true);
			runSpinner.setDisable(true);
			iterationSpinner.setDisable(true);
			toggleLineConstraints.setDisable(true);
			toggleQuadConstraints.setDisable(true);
			toggleBigRoomConstraint.setDisable(true);
			loadMousepoints.setDisable(true);
			saveMousepoints.setDisable(true);
			clearPane.setDisable(true);
			
			solverThread = new Thread(generateTask
			(
				runSpinner, roomSpinner, iterationSpinner,
				pane, controlLines, stop, mousepoints
			));
			solverThread.start();
			
			stop.setDisable(false);
			start.setDisable(true);
		});
		
		stop.setOnAction(e ->
		{
			loopCount = 0;
			runCount = 0;
			
			try
			{
				solver.interrupt();
				
			} catch(Z3Exception z) {}
			
			// enable all controls and disable stop button
			roomSpinner.setDisable(false);
			runSpinner.setDisable(false);
			iterationSpinner.setDisable(false);
			toggleLineConstraints.setDisable(false);
			toggleQuadConstraints.setDisable(false);
			toggleBigRoomConstraint.setDisable(false);
			loadMousepoints.setDisable(false);
			saveMousepoints.setDisable(false);
			clearPane.setDisable(false);
			
			start.setDisable(false);
			stop.setDisable(true);
		});
		
		/*
		scene.setOnKeyTyped(event ->
		{
			// below are controls for using the program
			switch(event.getCode())
			{
			// run the program if the user presses 'space'
			case SPACE:
				init_rooms(); // initialize dungeon rooms with their dimensions
				ctx = new Context();
				solver = ctx.mkSolver();
//				initAllConstraints(solver, mousepoints); // add all constraints to the solver
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
		*/
		
	}// end start
	
	private Task<Void> generateTask
	(
		Spinner<Integer> runSpinner, Spinner<Integer> roomSpinner, Spinner<Integer> iterationSpinner,
		Pane pane, Polyline controlLines, Button stop, ArrayList<Double> mousepoints
	){
		return new Task<Void>() {
			
			@Override
			protected Void call() throws Exception
			{
				// main starts here
				runCount = runSpinner.getValue();
				numberOfRooms = roomSpinner.getValue();
				int unsatCount = 0; // number of times the solver could not find a solution
				
				// format: [[x1, y1], [x2, y2], ..., [xn, yn]]
				// TODO may not need this data structure
				float[][] centerpoints;
				DelaunayTriangulator tri;
				HashMap<String, Long> timingInfo = new HashMap<>();
				
				long begin;
				long end;
				Status s;
				ArrayList<Edge> edges;
				KruskalMST graph;
				int[][] tcsr;
//				int i;
				solver = ctx.mkSolver();
				
				while(runCount > 0)
				{
					initRooms();
					displayRoomInfo(); // TODO not used for first run in original implementation
					solver.reset();
					initAllConstraints(solver, mousepoints);
					loopCount = iterationSpinner.getValue();
					
					while(loopCount > 0)
					{
//						Thread.sleep(1);
						Group group = new Group();
						begin = System.currentTimeMillis();
						s = solver.check();
						end = System.currentTimeMillis();
						System.out.println(s);
						System.out.println("Solve time: " + (end - begin) + " ms");
						// Traversing statistics
						BoolExpr[] asrts = solver.getAssertions();
						System.out.println("@@@ Assertions @@@");
//						i = 0;
//						for(BoolExpr asrt : asrts)
//						{
//							i = i + 1;
//							// System.out.println("Assertion: " + asrt);
//						}
						System.out.println("Total assertions: " + asrts.length);
						timingInfo.put("solveTime", end - begin);
						// if the solver found a satisfiable layout, display it to the user
						if(s == Status.SATISFIABLE)
						{
							begin = System.currentTimeMillis();
							centerpoints = computeRoomCenterpoints(solver.getModel());
							tri = new DelaunayTriangulator(convertPointsToVectors(centerpoints));	// use center points of rooms to initialize Delaunay object
							tri.triangulate();
							end = System.currentTimeMillis();
							timingInfo.put("delaunayTime", end - begin);
							begin = System.currentTimeMillis();
							edges = new ArrayList<>();
							
							// TODO may not need this data structure
							double[][] ar = createGraphArray(tri, centerpoints, edges);	// create matrix containing length of edges between nodes of Delaunay triangulation
							graph = new KruskalMST(rooms.size());
							graph.Kruskal(edges.toArray(new Edge[edges.size()]));
							tcsr = getMst(graph.getVertices());		// get the "compressed-sparse representation of the undirected minimum spanning tree"
							end = System.currentTimeMillis();
							timingInfo.put("mstTime", end - begin);
							drawRooms(solver.getModel(), group, tri, tcsr, centerpoints, mousepoints);
							updateGrid(solver.getModel());
							loopCount--;
							updateTiming();
							Platform.runLater(new Runnable()
							{
								@Override
								public void run()
								{
									pane.getChildren().retainAll(controlLines);
									pane.getChildren().add(group);
								}
							});
							
						} else {
							
							System.out.println("Cannot find room placement!");
							displayRoomInfo();
							initRooms();
							loopCount = NUM_LOOPS;
							unsatCount++;	// TODO this number is never reset
							if(unsatCount > 10)
							{
								Platform.runLater(new Runnable()
								{
									@Override
									public void run()
									{
										ctx.close();
										System.exit(1);
									}
								});
							}
							
						}// end if
						
					}// end while
					
					runCount--;
					//saveAccumulatedTiming();
					System.out.println("#######\nRun: " + runCount + "\n#######");
					
				}// end while
				
				makeHeatmap();
				finalDataAnalysis();
				
				Platform.runLater(new Runnable()
				{
					@Override
					public void run()
					{
						controlLines.getPoints().clear();
//						pane.getChildren().retainAll(controlLines);
					}
				});
				
				if(!stop.isDisabled())
				{
					stop.fire();
				}
				
				return null;
				
			}// end call
		};
	}
	
}// end Smt_Dungeon
