package edu.csupomona.spring2023.cs5990.PCG_Dungeon_Implementation;

import javafx.application.Application;
import javafx.stage.Stage;
import javafx.scene.Scene;
import javafx.scene.layout.HBox;
import javafx.scene.paint.Color;
import javafx.scene.shape.Rectangle;
import javafx.scene.shape.Polygon;
import javafx.scene.control.Button;

import java.util.ArrayList;
import java.util.HashMap;
//import java.util.Random;

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

	/*
	public ArrayList<ArrayList<Long>> compute_room_centerpoints(Model m){
		ArrayList<ArrayList<Long>> cp = new ArrayList<>();
		
		for(int i = 0; i < number_of_rooms; i++){
			rooms.get(i).put("x_center", )
		}
	}
	*/

	// TODO implement draw_rooms, draw_lines, and draw_passageways
	private void drawRooms(Model m, DelaunayTriangulator tri, KruskalMST mst, double[] centerPoints, double[] mousePoints)
	{
		Rectangle rectangle;
		for(int i = 0; i < number_of_rooms; i++)
		{
			rectangle = new Rectangle(/*(m[rooms[i]['x']].as_long() + BORDER), (m[rooms[i]['y']].as_long())/SCALE_FACTOR+BORDER, rooms[i]['width'], rooms[i]['height']/SCALE_FACTOR*/);
			rectangle.setStrokeWidth(2);
			
			switch(rooms.get(i).getQuad())
			{
			case 1:
				// Default color of rectangle is already black
				break;
			case 2:
				rectangle.setFill(Color.ORANGE);
				break;
			case 3:
				rectangle.setFill(Color.BLUE);
				break;
			case 4:
				rectangle.setFill(Color.GREEN);
				break;
			default:
				break;
			}// end switch
			
		}// end for
		
		if(true/*triangulation != null*/)
		{
			Double[] points = new Double[6];
			/* TODO = new double[DelaunayTriangulator.getTriangles().size() * 6]*/
			/* TODO int i = 0;*/	// base index for adding triangle coordinates to points
			// Draw Delaunay triangulation
			for(;;/*Triangle2D triangle : DelaunayTriangulator.getTriangles()*/)
			{
				//System.out.println("t is " + triangle);
//				points[/*i + */0]pointList(triangle.a.x + BORDER);
//				points[/*i + */1]points((triangle.a.y / SCALE_FACTOR) + BORDER);
//				points[/*i + */2]points(triangle.b.x + BORDER);
//				points[/*i + */3]points((triangle.b.y / SCALE_FACTOR) + BORDER);
//				points[/*i + */4]points(triangle.c.x + BORDER);
//				points[*/i + */5]points((triangle.c.y / SCALE_FACTOR) + BORDER);
				/* TODO i += 5;*/
				if(showDelaunay)
				{
					Polygon lines = new Polygon();
					lines.getPoints().addAll(points);
					lines.setFill(null);
					lines.setStroke(Color.DARKBLUE);
//					SOMENODE.getChildren().add(lines);
				}
				break;// TODO remove after implementation of for loop is complete
			}
		}
		
		if(true/*minimumSpanningTree != null*/)
		{
			
		}
		
	}// end drawRooms
	
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
		ArrayList<double[]> centerPoints  = new ArrayList<>();
		
//		initGridCounts();					// counts the number of grid cells within the play area
		DelaunayTriangulator tri;
//		mousepoints array/dictionary		// data structure containing points for control lines specified by the user
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
//					centerPoints = computeRoomCenterpoints(solver.getModel());
//			TODO		tri = DelaunayTriangulator(centerPoints);	// use center points of rooms to initialize Delaunay object
//					end = System.currentTimeMillis();
//					timing_info['delaunay_time'] = end - begin
//					begin = System.currentTimeMillis();
//					ar = create_graph_array(tri, center_points)	// create matrix containing length of edges between nodes of Delaunay triangulation
//					tcsr = minimum_spanning_tree(ar)		// get the "compressed-sparse representation of the undirected minimum spanning tree"
//					end = System.currentTimeMillis();
//					timing_info['mst_time'] = end - begin
//					draw_rooms(solver.model(), surface, tri, tcsr, centerPoints, mousepoints)
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
