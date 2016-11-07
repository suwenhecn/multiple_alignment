
public class Console {
	  public static void illustrate(){
		    System.out.println("The command should be");
		    System.out.println("  Improvecenterstar inputfile [0/1]");
		    System.out.println("    -0: center star method for multiple sequence alignment");
		    System.out.println("    -1: improved center star method for multiple sequence alignment(default)");
		  }

	public static void main(String[] args) {
		// TODO Auto-generated method stub
		try{
			
		      long t1 = System.currentTimeMillis();


              //args=["0","1"];
		      boolean improved = true; //如果improved为true，则使用改进的星比对算法；否则使用原始的星比对算法
		      if(args.length==2&&args[1].equals("0"))
		        improved = false;
		      else if(args.length==2&&args[1].equals("1"))
		        improved = true;
		      /*
		      else if(args.length!=1){
		        illustrate();
		        System.exit(0);
		      }
		      */
		      improved=true;
		      //MSA program = new MSA(args[0]);
		      MSA program= new MSA("KAsq.txt");
		      //MSA program= new MSA("input1.fasta");
		      if (improved == true) //使用改进后的星比对算法
		        program.runforimproved();
		      else if (improved == false) //使用原始星比对算法
		        program.runforold();

		      long t2 = System.currentTimeMillis();
		      System.out.print("程序运行时间是");
		      System.out.print(t2 - t1);
		      System.out.println("毫秒");
		    }
		    catch(Exception ex){
		      System.out.println(ex.getMessage());
		    }
		        }

	}


