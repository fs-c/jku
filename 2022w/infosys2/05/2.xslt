<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns:xs="http://www.w3.org/2001/XMLSchema" xmlns:fn="http://www.w3.org/2005/xpath-functions" xmlns:math="http://www.w3.org/2005/xpath-functions/math" xmlns:array="http://www.w3.org/2005/xpath-functions/array" xmlns:map="http://www.w3.org/2005/xpath-functions/map" xmlns:xhtml="http://www.w3.org/1999/xhtml" xmlns:err="http://www.w3.org/2005/xqt-errors" exclude-result-prefixes="array fn map math xhtml xs err" version="3.0">
	<xsl:output method="html" version="5.2" encoding="UTF-8" indent="yes"/>
	<xsl:template match="Firma" name="xsl:initial-template">
		<html>
		<body style="font-family: Verdana;">
			<h3>New Employees</h3>
			
			<xsl:apply-templates />
		</body>
		</html>
	</xsl:template>
	
	<xsl:template match="Abteilung">
		<h4>
			Department: <xsl:value-of select="AbteilungsName" />
		</h4>
		
		<p>
			Location: <xsl:value-of select="Ort" /> <br />
			Total Employees: <xsl:value-of select="count(Mitarbeiter)" />
		</p>
		
		<xsl:choose>
			<xsl:when test="count(Mitarbeiter[Einstellungsjahr = 2022])">
				<p>New Employees:</p>
				
				<table border="1">
				<tbody>
					<tr bgcolor="#ACCDDE">
						<th>EmpNo</th>
						<th>Name</th>
						<th>Weekly Salary</th>
					</tr>
					
					<xsl:for-each select="Mitarbeiter[Einstellungsjahr = 2022]">
						<tr>
							<td><xsl:value-of select="Nr" /></td>
							<td><xsl:value-of select="Name" /></td>
							<td><xsl:value-of select="Gehalt" /></td>
						</tr>
					</xsl:for-each>
				</tbody>
			</table>
			</xsl:when>
			
			<xsl:otherwise>
				<xsl:choose>
					<xsl:when test="count(Mitarbeiter) != 0">
						<p>
							New Employees: <span style="color: red;">No new employees in this department!</span>
						</p>
					</xsl:when>
				</xsl:choose>
			</xsl:otherwise>
		</xsl:choose>
	</xsl:template>
</xsl:stylesheet>
