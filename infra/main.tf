# Provider Configuration
terraform {
  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = "5.57.0"
    }
  }
}

# Configure the AWS Provider
provider "aws" {
  region = "us-east-1"
}

# to manage access to the GitHub Container Registry
resource "aws_secretsmanager_secret" "ghcr_credentials" {
  name = "ghcr-credentials"
}

resource "aws_secretsmanager_secret_version" "ghcr_credentials" {
  secret_id     = aws_secretsmanager_secret.ghcr_credentials.id
  secret_string = jsonencode({
    username = var.ghcr-pat,
    password = var.ghcr-pat,
  })
}

resource "aws_iam_role" "leios_task_execution_role" {
  name               = "leios-task-execution-role"
  assume_role_policy = data.aws_iam_policy_document.ecs_task_assume_role.json
}

data "aws_iam_policy_document" "ecs_task_assume_role" {
  statement {
    actions = ["sts:AssumeRole"]

    principals {
      type = "Service"
      identifiers = ["ecs-tasks.amazonaws.com"]
    }
  }
}

data "aws_iam_policy" "ecs_task_execution_role" {
  arn = "arn:aws:iam::aws:policy/service-role/AmazonECSTaskExecutionRolePolicy"
}

# Attach the above policy to the execution role.
resource "aws_iam_role_policy_attachment" "ecs_task_execution_role" {
  role       = aws_iam_role.leios_task_execution_role.name
  policy_arn = data.aws_iam_policy.ecs_task_execution_role.arn
}

# VPC Creation
resource "aws_vpc" "leios_vpc" {
  cidr_block           = "10.0.0.0/16"
  enable_dns_support   = true
  enable_dns_hostnames = true
}

resource "aws_subnet" "leios_subnet" {
  vpc_id     = aws_vpc.leios_vpc.id
  cidr_block = "10.0.1.0/24"
}

# Security Group Creation
resource "aws_security_group" "leios_security_group" {
  name_prefix = "leios-security-group"
  vpc_id      = "${aws_vpc.leios_vpc.id}"
  ingress {
    from_port   = 8000
    to_port     = 9000
    protocol    = "tcp"
    cidr_blocks = ["0.0.0.0/0"]
  }
  egress {
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }
}

# ECS Cluster Creation
resource "aws_ecs_cluster" "leios_cluster" {
  name = "leios-cluster"
}

# ECS Task Definition Creation
resource "aws_ecs_task_definition" "leios_task_definition" {
  family                   = "leios-task-definition"
  requires_compatibilities = ["FARGATE"]
  network_mode             = "awsvpc"
  cpu                      = 256
  memory                   = 512
#  task_role_arn            = aws_iam_role.github_role.arn
  execution_role_arn       = aws_iam_role.leios_task_execution_role.arn

  container_definitions = jsonencode([
    {
      name               = "leios-container"
      image              = "${var.repository}/${var.image}:${var.tag}"
      memory_reservation = 256
      repositoryCredentials = {
        credentialsParameter = aws_secretsmanager_secret.ghcr_credentials.id
      },
      portMappings = [
        {
          containerPort = 8091
          hostPort      = 8091
        }
      ]
    }
  ])
}

# ECS Service Creation
resource "aws_ecs_service" "leios_service" {
  name            = "leios-service"
  cluster         = aws_ecs_cluster.leios_cluster.id
  task_definition = aws_ecs_task_definition.leios_task_definition.arn
  desired_count   = 1
  launch_type     = "FARGATE"

  network_configuration {
    subnets          = aws_subnet.leios_subnet.*.id
    security_groups  = [ aws_security_group.leios_security_group.id]
    assign_public_ip = true
  }
}
