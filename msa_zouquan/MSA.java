import java.io.*;
import java.util.ArrayList;
import java.util.Arrays;

/**
 * <p>
 * Title:
 * </p>
 * <p>
 * Description:
 * </p>
 * <p>
 * Copyright: Copyright (c) 2016
 * </p>
 * <p>
 * Company:
 * </p>
 * 
 * @author 邹权
 * @version 2016年2月27日
 */

public class MSA {
	String filepath = ""; // 记录文件名称
	String Pi[]; // 记录每一个序列
	String Piname[]; // 记录每一个序列的名字
	int Spaceevery[][]; // 存放中心序列分别与其他序列比对时增加的空格的位置
	int Spaceother[][]; // 存放其他序列与中心序列比对时增加的空格的位置
	int n; // 存放序列个数
	int center; // 存放中心序列编号
	int spacescore = -1, matchscore = 0, mismatchscore = -1; // ###########定义匹配，不匹配和空格的罚分###############
	int Name[][][][]; // 树搜索完，记录匹配的区域;四维数组，第一位是Pi[i],第二位是pi[j]，记录两个序列的标号，第3维是3，Name[i][j][0][k]记录的是Pi[i]中的起始位置
						// Name[i][j][1][k] 记录的是Pi[j]中的起始位置
						// Name[i][j][2][k] 记录的是匹配的长度

	public MSA(String Path) {
		filepath = Path;
	}

	// 计算序列个数
	public int countnum() {
		int num = 0;
		try {
			BufferedReader br = new BufferedReader(new FileReader(filepath));
			String s;
			while (br.ready()) {
				s = br.readLine();
				if (s.charAt(0) == '>')
					num++;
			}
			br.close();
		} catch (Exception ex) {
		}
		return (num);
	}

	// 将序列一次读入数组中
	public void input() {
		Pi = new String[n];
		Piname = new String[n];
		int i = 0;
		try {
			BufferedReader br = new BufferedReader(new FileReader(filepath));

			String BR = br.readLine();
			while (br.ready()) {

				if (BR.length() != 0 && BR.charAt(0) == '>') {
					Piname[i] = BR;
					Pi[i] = "";
					while (br.ready() && (BR = br.readLine()).charAt(0) != '>') {
						Pi[i] += BR;
					}
					Pi[i] = format(Pi[i]);
					i++;
				} else
					BR = br.readLine();
			}

			br.close();
		} catch (Exception ex) {
			System.out.println(ex.getMessage());
			System.exit(0);
		}
	}

	// 找出Num[][]数组中和最大的那一行
	public int findNumMax(int Num[][]) {
		int Numsum[] = new int[n];
		for (int i = 0; i < n; i++) {
			Numsum[i] = 0;
			for (int j = 0; j < n; j++)
				Numsum[i] = Numsum[i] + Num[i][j];
		}
		int tmpcenter = 0;
		for (int i = 1; i < n; i++) {
			if (Numsum[i] > Numsum[tmpcenter])
				tmpcenter = i;
		}
		return (tmpcenter);
	}

	/**
	 * 对String格式化,删除非法字符(只保留agctn,其余字符全部替换成n),全部转换成小写,u全部换成t
	 * 
	 * @param s
	 * @return
	 */
	public String format(String s) {
		s = s.toLowerCase();
		s = s.replace('u', 't');
		StringBuffer sb = new StringBuffer(s);

		for (int i = 0; i < sb.length(); i++) {
			switch (sb.charAt(i)) {
			case 'a':
				break;
			case 'c':
				break;
			case 'g':
				break;
			case 't':
				break;
			case 'n':
				break;
			default:
				sb = sb.replace(i, i + 1, "n");
			}
		}
		return (sb.toString());
	}

	// 找出中心序列
	public int findCenterSeq() {

		Name = new int[n][n][3][]; // 用来存放出现的名字，Name[i][j][0][k]和Name[i][j][1][k]表示了Pi[i]序列的第Name[i][j][0][k]个片段出现在Pi[j]序列的Name[i][j][1][k]位置上



			SuffixTree st1 = new SuffixTree();
			st1.build(Pi[0] + "$");
			

			for (int j = 1; j < n; j++) {
				//从一开始开始查找
				int index = 0;

				int totalmatch = 0;
				ArrayList<Integer> result = new ArrayList();
				while (index < Pi[j].length()) {
					int[] a = st1.selectPrefixForAlignment(Pi[j], index);
					if (a[1] > Math.abs(a[0] - index)) {
						result.add(a[0]);
						result.add(index);
						result.add(a[1]);
						index += a[1];
						totalmatch += a[1];
					} else if (a[1] > 0)
						index += a[1];
					else
						index++;
				}
	
				int[][] tmp = new int[3][result.size() / 3];
				int k = 0;
				while (k < result.size()) {
					tmp[0][k / 3] = result.get(k);
					k++;
					tmp[1][k / 3] = result.get(k);
					k++;
					tmp[2][k / 3] = result.get(k);
					k++;
				}
				Name[0][j] = tmp;

			}

		

		return (0);
	}

	// 在动态规划中计算矩阵积分
	public int[][] computeScoreMatrixForDynamicProgram(String stri, String strC) {
		int len1 = stri.length() + 1;
		int len2 = strC.length() + 1;
		int M[][] = new int[len1][len2]; // 定义动态规划矩阵
		// ---初始化动态规划矩阵-----------
		int p, q;

		for (p = 0; p < len1; p++)
			M[p][0] = spacescore * p;
		for (q = 0; q < len2; q++)
			M[0][q] = spacescore * q;
		// ---初始化结束----------
		// ----计算矩阵的值------------
		for (p = 1; p < len1; p++)
			for (q = 1; q < len2; q++) {// M[p][q]=max(M[p-1][q]-1,M[p][q-1]-1,M[p-1][q-1]+h)
				int h;
				if (stri.charAt(p - 1) == strC.charAt(q - 1))
					h = matchscore;
				else
					h = mismatchscore;
				M[p][q] = Math.max(M[p - 1][q - 1] + h, Math.max(M[p - 1][q] + spacescore, M[p][q - 1] + spacescore));
			}
		return (M);
	}

	// 在动态规划中回溯
	public void traceBackForDynamicProgram(int[][] M, int p, int q, int i, int k1, int k2) {
		while (p > 0 && q > 0) {
			if (M[p][q] == M[p][q - 1] + spacescore) {
				Spaceother[i][p + k1]++;
				q--;
			} else if (M[p][q] == M[p - 1][q] + spacescore) {
				Spaceevery[i][q + k2]++;
				p--;
			} else {
				p--;
				q--;
			}
		}
		if (p == 0)
			while (q > 0) {
				Spaceother[i][k1]++;
				q--;
			}
		if (q == 0)
			while (p > 0) {
				Spaceevery[i][k2]++;
				p--;
			}
	}

	// 比对Pi[i]与中心序列有重合的前端
	public void prealign(int i) {

		String strC = Pi[center].substring(0, Name[center][i][0][0]);
		String stri = Pi[i].substring(0, Name[center][i][1][0]);
		int M[][] = new int[stri.length() + 1][strC.length() + 1]; // 定义动态规划矩阵
		M = computeScoreMatrixForDynamicProgram(stri, strC);// 动态规划矩阵计算完毕
		traceBackForDynamicProgram(M, stri.length(), strC.length(), i, 0, 0);// 回溯，更改空格数组

	}

	// 比对Pi[i]与中心序列有重合的中间部分
	public void midalign(int i, int j) {
		
		int lamda = Math.max(Name[center][i][1][j - 1] + Name[center][i][2][j - 1] - Name[center][i][1][j],
				Name[center][i][0][j - 1] + Name[center][i][2][j - 1] - Name[center][i][0][j]);
		// lamda是为了防止前后两块完全匹配有覆盖，把覆盖部分删除
		if (lamda > 0) {
			Name[center][i][0][j] += lamda;
			Name[center][i][1][j] += lamda;
			Name[center][i][2][j] -= lamda;
		}
		if (Name[center][i][2][j] < 0)
			System.out.println("此处有错误！！！！");

		String strC = Pi[center].substring(Name[center][i][0][j - 1] + Name[center][i][2][j - 1],
				Name[center][i][0][j]);// 此处有漏洞，如果Name[center][i][0][0]=0，会抱错
	
		String stri = Pi[i].substring(Name[center][i][1][j - 1] + Name[center][i][2][j - 1], Name[center][i][1][j]);

		int M[][] = new int[stri.length() + 1][strC.length() + 1]; // 定义动态规划矩阵
		M = computeScoreMatrixForDynamicProgram(stri, strC);// 动态规划矩阵计算完毕
		traceBackForDynamicProgram(M, stri.length(), strC.length(), i,
				Name[center][i][1][j - 1] + Name[center][i][2][j - 1],
				Name[center][i][0][j - 1] + Name[center][i][2][j - 1]);

	}

	// 比对Pi[i]与中心序列有重合的后端
	public void postalign(int i) {

		int j = Name[center][i][0].length;
		if (j > 0) {
			int cstart = Name[center][i][0][j - 1] + Name[center][i][2][j - 1];
			if (cstart > Pi[center].length())
				cstart--;// 别忘了，建后缀树时加了个$
			int istart = Name[center][i][1][j - 1] + Name[center][i][2][j - 1];
			if (istart > Pi[i].length())
				istart--;

			
			String strC = Pi[center].substring(cstart);

			String stri = Pi[i].substring(Name[center][i][1][j - 1] + Name[center][i][2][j - 1]);

			int M[][] = new int[stri.length() + 1][strC.length() + 1]; // 定义动态规划矩阵

			M = computeScoreMatrixForDynamicProgram(stri, strC);// 动态规划矩阵计算完毕

			traceBackForDynamicProgram(M, stri.length(), strC.length(), i,istart,cstart);

		} else {
			String strC = Pi[center];
			String stri = Pi[i];
			int M[][] = new int[stri.length() + 1][strC.length() + 1]; // 定义动态规划矩阵
			M = computeScoreMatrixForDynamicProgram(stri, strC);// 动态规划矩阵计算完毕
			traceBackForDynamicProgram(M, stri.length(), strC.length(), i, 0, 0);
		}
	}

	// 将Pi[i]与中心序列进行比对
	public void pairwiseAlignForImproved(int i) {
		prealign(i);

		for (int j = 1; j < Name[center][i][0].length; j++) {

			midalign(i, j);
		}

		postalign(i);

	}

	public void pairwiseAlignForOld(int i) {
		int M[][] = new int[Pi[i].length() + 1][Pi[center].length() + 1];
		M = computeScoreMatrixForDynamicProgram(Pi[i], Pi[center]);// 动态规划矩阵计算完毕
		traceBackForDynamicProgram(M, Pi[i].length(), Pi[center].length(), i, 0, 0);
	}

	public int[] combine() {
		int Space[] = new int[Pi[center].length() + 1];// 该数组用来记录在P[center]的最终结果各个空隙间插入空格的个数
		int i, j;
		for (i = 0; i < Pi[center].length() + 1; i++) {
			int max = 0;
			for (j = 0; j < n; j++)
				if (Spaceevery[j][i] > max)
					max = Spaceevery[j][i];
			Space[i] = max;
		}
		return (Space);
	}

	// 计算除中心序列以外的其他序列的最大长度
	public int computeMaxLength(int center) {
		int maxlength = 0;
		for (int i = 0; i < n; i++) {
			if (i == center)
				continue;
			if (Pi[i].length() > maxlength)
				maxlength = Pi[i].length();
		}
		return (maxlength);
	}

	// 多序列比对部分
	public void mutipleSequenceAlign(boolean improved) {
		Spaceevery = new int[n][Pi[center].length() + 1];// 存放中心序列分别与其他序列比对时增加的空格的位置
		Spaceother = new int[n][computeMaxLength(center) + 1];// 存放其他序列与中心序列比对时增加的空格的位置
		for (int i = 0; i < n; i++) {

			if (i == center)
				continue;
			if (improved == true)
				pairwiseAlignForImproved(i);
			else if (improved == false)
				pairwiseAlignForOld(i);
		}
		int Space[] = new int[Pi[center].length() + 1];// 该数组用来记录在P[center]的最终结果各个空隙间插入空格的个数
		Space = combine();
		output(Space);
	}

	public void output(int[] Space) {
		int i, j;
		// ---------输出中心序列----------
		String PiAlign[] = new String[n];
		PiAlign[center] = "";
		for (i = 0; i < Pi[center].length(); i++) {
			for (j = 0; j < Space[i]; j++)
				PiAlign[center] = PiAlign[center].concat("-");
			PiAlign[center] = PiAlign[center].concat(Pi[center].substring(i, i + 1));
		}
		for (j = 0; j < Space[Pi[center].length()]; j++)
			PiAlign[center] = PiAlign[center].concat("-");
		// --------中心序列输出完毕------
		// ---------输出其他序列-------
		for (i = 0; i < n; i++) {
			if (i == center)
				continue;
			// ----计算和中心序列比对后的P[i],记为Pi-----
			PiAlign[i] = "";
			for (j = 0; j < Pi[i].length(); j++) {
				String kong = "";
				for (int k = 0; k < Spaceother[i][j]; k++)
					kong = kong.concat("-");
				PiAlign[i] = PiAlign[i].concat(kong).concat(Pi[i].substring(j, j + 1));
			}
			String kong = "";
			for (j = 0; j < Spaceother[i][Pi[i].length()]; j++)
				kong = kong.concat("-");
			PiAlign[i] = PiAlign[i].concat(kong);

			// ---Pi计算结束---------
			// ----计算差异数组----
			int Cha[] = new int[Pi[center].length() + 1];
			int position = 0; // 用来记录插入差异空格的位置
			for (j = 0; j < Pi[center].length() + 1; j++) {
				Cha[j] = 0;
				if (Space[j] - Spaceevery[i][j] > 0)
					Cha[j] = Space[j] - Spaceevery[i][j];
				// ----差异数组计算完毕---
				// ----填入差异空格----
				position = position + Spaceevery[i][j];
				if (Cha[j] > 0) { // 在位置position处插入Cha[j]个空格
					kong = "";
					for (int k = 0; k < Cha[j]; k++)
						kong = kong.concat("-");
					PiAlign[i] = PiAlign[i].substring(0, position).concat(kong).concat(PiAlign[i].substring(position));
				}
				position = position + Cha[j] + 1;
				// ----差异空格填入完毕--
			}
		}
		try {
			BufferedWriter bw = new BufferedWriter(new FileWriter("output.txt"));
			for (i = 0; i < n; i++) {
				// System.out.println(Piname[i]);
				bw.write(Piname[i]);
				bw.newLine();
				bw.flush();
				// System.out.println(PiAlign[i]);
				bw.write(PiAlign[i]);
				bw.newLine();
				bw.flush();

			}
			bw.close();
		} catch (Exception ex) {

		}
		// ---------其他序列输出完毕-----
		// ---------输出结束--------------

	}

	// 计算原始星比对中sim矩阵的值
	public int[][] computesim() {
		int[][] sim = new int[n][n];
		int i, j;
		// 计算上三角
		for (i = 0; i < n; i++)
			for (j = i + 1; j < n; j++) {
				int M[][] = new int[Pi[i].length() + 1][Pi[j].length() + 1];
				M = computeScoreMatrixForDynamicProgram(Pi[i], Pi[j]);// 动态规划矩阵计算完毕
				sim[i][j] = M[Pi[i].length()][Pi[j].length()];
			}
		// -----计算sim[][]的下三角
		for (i = 0; i < n; i++)
			sim[i][i] = 0;
		for (i = 1; i < n; i++)
			for (j = 0; j < i; j++)
				sim[i][j] = sim[j][i];
		return (sim);
	}

	// 改进的星比对算法
	public void runforimproved() {
		long t1 = System.currentTimeMillis();
		n = countnum();// 记录序列的个数
		input();
		center = findCenterSeq();

		long t2 = System.currentTimeMillis();
	      System.out.print("寻找中心序列程序运行时间是");
	      System.out.print(t2 - t1);
	      System.out.println("毫秒");
		mutipleSequenceAlign(true);
		
		long t3 = System.currentTimeMillis();
	      System.out.print("对齐程序运行时间是");
	      System.out.print(t3 - t2);
	      System.out.println("毫秒");
	}

	// 原始的星比对算法
	public void runforold() {
		n = countnum();// 记录序列的个数
		input();
		center = findNumMax(computesim());
		System.out.println("中心序列是第" + center + "条！");
		mutipleSequenceAlign(false);
	}

}
