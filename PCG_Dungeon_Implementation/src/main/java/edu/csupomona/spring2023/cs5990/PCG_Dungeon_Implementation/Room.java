package edu.csupomona.spring2023.cs5990.PCG_Dungeon_Implementation;

import com.microsoft.z3.Context;
import com.microsoft.z3.IntExpr;

/**
 * Data structure containing fields for rooms.
 * @author Payton Perchez
 */
public class Room {

	private IntExpr x;	// x-coordinate
	private IntExpr y;	// y-coordinate
	private int width;
	private int height;
	private int quad;	// quadrant (1-4)
	
	public Room(Context ctx, int roomNum)
	{
		this(ctx.mkIntConst("room_" + roomNum + "_x"), ctx.mkIntConst("room_" + roomNum + "_y"), 0, 0, 0);
		
	}
	
	public Room(IntExpr x, IntExpr y, int width, int height, int quad)
	{
		this.x = x;
		this.y = y;
		this.width = width;
		this.height = height;
		this.quad = quad;
		
	}
	
	public IntExpr getX()
	{
		return x;
	}
	
	public IntExpr getY()
	{
		return y;
	}
	
	public int getWidth()
	{
		return width;
	}
	
	public int getHeight()
	{
		return height;
	}
	
	public int getQuad()
	{
		return quad;
	}
	
	public void setX(IntExpr newX)
	{
		x = newX;
	}
	
	public void setY(IntExpr newY)
	{
		y = newY;
	}
	
	public void setWidth(int newWidth)
	{
		width = newWidth;
	}
	
	public void setHeight(int newHeight)
	{
		height = newHeight;
	}
	
	public void setQuad(int newQuad)
	{
		quad = newQuad;
	}
	
}// end Room
