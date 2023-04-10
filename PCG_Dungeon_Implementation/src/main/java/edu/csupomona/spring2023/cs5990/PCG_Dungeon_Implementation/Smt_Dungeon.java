package edu.csupomona.spring2023.cs5990.PCG_Dungeon_Implementation;

import javafx.application.Application;
import javafx.stage.Stage;
import javafx.scene.Scene;
import javafx.scene.layout.HBox;
import javafx.scene.paint.Color;
import javafx.scene.shape.Rectangle;
import javafx.scene.shape.Polygon;
import javafx.scene.control.Button;

import java.util.HashMap;
//import org.sosy_lab.java_smt.SolverContextFactory;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Context;

/**
 * Java implementation of Jim Whitehead's procedural dungeon generation algorithm
 * Source: (https://github.com/JimWhiteheadUCSC/smt_dungeon)
 * @author Jack Peabody
 * @author Payton Perchez
 */
public class Smt_Dungeon extends Application
{
	private		final	int			NUM_ROOMS			= 30;			// Default number of rooms
	private				int			numberOfRooms		= NUM_ROOMS;	// The number of rooms (which the user can change)
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
	private				boolean		bigRoomConstraints	= false;
	private				boolean		showDelaunay		= false;
	private				boolean		showSparse			= false;
	private				int[]		rooms;
	private				int[]		assumptions;
//	private		static	HashMap<String, String> directions = new HashMap<>();
//	static
//	{
//		directions.put("vert", "above");
//		directions.put("vert", "above");
//	}
	private				int			andClauseCount		= 0;
	private				int			orClauseCount		= 0;
	private				boolean		runOnce				= false;	// only runs the program once if true
	private				boolean		looper				= true;		// keeps the program running
	
	private				Solver		solver;
	private				Context		ctx;
	
	/* TODO
	 * Download the following classes from https://github.com/kevalmorabia97/Graph-Theory-Implementations-in-Java (don't forget about MIT license)
	 *  - Graph.java
	 *  - KruskalMST.java
	 *  - Vertex.java
	 * Can use maven to download dependencies from https://github.com/jfree
	 * Can use maven to download dependencies from https://github.com/jdiemke/delaunay-triangulator
	 */
	
	public static void main(String[] args)
	{
		//-Djava.library.path=C:\Users\payto\MySoftware\z3-4.12.1-x64-win\bin\libz3java.dll
//		System.setProperty("java.library.path", "C:/Users/payto/MySoftware/z3-4.12.1-x64-win/bin/libz3java.dll");
		launch(args);
	}
	// TODO implement draw_rooms, draw_lines, and draw_passageways
	private void drawRooms(/*m, DelaunayTriangulator, minimumSpanningTree, centerPoints, mousePoints*/)
	{
		Rectangle rectangle;
		for(int i = 0; i < numberOfRooms; i++)
		{
			rectangle = new Rectangle(/*(m[rooms[i]['x']].as_long() + BORDER), (m[rooms[i]['y']].as_long())/SCALE_FACTOR+BORDER, rooms[i]['width'], rooms[i]['height']/SCALE_FACTOR*/);
			rectangle.setStrokeWidth(2);
			
			switch(rooms[i]/*['quad']*/)
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
//		centerPoints array/dictionary
//		initGridCounts();					// counts the number of grid cells within the play area
//		Delaunay tri
//		mousepoints array/dictionary		// data structure containing points for control lines specified by the user
//		timingInfo dictionary
		long begin;
		long end;
		int i;
		
		looper = false;// TODO delete after moving the following while loop out of the application thread
		
		while(looper)
		{
			if(runOnce)
			{
//				time.sleep(1);
				begin = System.currentTimeMillis();
//				s = solver.check();
				end = System.currentTimeMillis();
//				System.out.println(s);
//				System.out.println("Solve time: " + ((end - begin) * 1000) + " ms");
				// Traversing statistics
//				asrts = solver.assertions()
//				System.out.println("@@@ Assertions @@@");
				i = 0;
//				for(asrt : asrts)
//				{
//					i = i + 1;
					//print("Assertion: " + asrt)
//				}
//				print("Total assertions: " + i);
//				timingInfo['solveTime'] = end - begin;
				// if the solver found a satisfiable layout, display it to the user
//				if(s.r == Z3_L_TRUE)
//				{
//					//displayRoomPlusModel(solver.model);
//					begin = System.currentTimeMillis();
//					centerPoints = computeRoomCenterpoints(solver.model());
//					tri = Delaunay(centerPoints);	// use center points of rooms to initialize Delaunay object
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
//				}// end if
				
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
		Scene scene = new Scene(new HBox(testButton));
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
//				System.out.println("yoyoyo");
//				ctx = new Context();
//				solver = ctx.mkSolver();
//				System.out.println(solver.check());
//				solver = Solver()
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
				numberOfRooms += 1;
				break;
				
			case MINUS:
				numberOfRooms -= 1;
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
//				mousepoints = loadMousepointsData();
				break;
				
//			case Z:
//				break;
				
			default:
				break;
			}// end switch
		});
		
		scene.setOnMouseClicked(event ->
		{
//			if event.button == 1
//				mousepoints.append(event.pos);
//				System.out.println("Added: " + event.pos);
//				drawLines(surface, mousepoints);
		});
	}// end start
	
}// end Smt_Dungeon
